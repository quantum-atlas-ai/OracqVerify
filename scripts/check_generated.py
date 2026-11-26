"""Exercise the Lean command line against the pinned Oracq runtime."""

import cmath
import json
import math
from pathlib import Path
import subprocess
import tempfile
import unittest

from oracq import (
    Binding, Bits, Builder, QRAM, ValidationError, bind, dumps, estimate_resources, fuse, loads,
    simulate, unresolved,
)
from oracq.algorithms.basics.oracle_algorithms import deutsch_jozsa
from oracq.algorithms.input_model.oracles import abstract_database, declare


ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / ".lake" / "build" / "bin" / "oracq-verify"
DJ_THEOREM = "OracqVerify.Generators.DeutschJozsa.generate_correct"


def command(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [CLI, *args], check=False, text=True, capture_output=True, timeout=30
    )


def resolve(program: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "program.json"
        path.write_text(program, encoding="utf-8")
        return command("resolve", str(path))


class GeneratorChecks(unittest.TestCase):
    def test_registry_and_invalid_parameters(self) -> None:
        listing = command("list")
        self.assertEqual(listing.returncode, 0, listing.stderr)
        self.assertIn(f"{DJ_THEOREM} <address-width>", listing.stdout)
        for request, message in (
            (("generate", "unknown", "1"), "Unknown generator theorem"),
            (("generate", DJ_THEOREM, "0"), "positive integer"),
            (("generate", DJ_THEOREM, "abc"), "positive integer"),
            (("generate", DJ_THEOREM), "one argument"),
        ):
            with self.subTest(request=request):
                result = command(*request)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertIn(message, result.stderr)

    def test_leans_dj_opens_resolves_and_binds_in_oracq(self) -> None:
        for width in (1, 3, 65):
            with self.subTest(width=width):
                generated = command("generate", DJ_THEOREM, str(width))
                self.assertEqual(generated.returncode, 0, generated.stderr)
                program = loads(generated.stdout)
                self.assertEqual([reg.type.width for reg in program.main.registers], [width, 1])
                self.assertEqual([slot.name for slot in unresolved(program)], ["dj_function"])
                with tempfile.TemporaryDirectory() as directory:
                    path = Path(directory) / "lean.open.json"
                    path.write_text(generated.stdout, encoding="utf-8")
                    checked = command("verify", DJ_THEOREM, str(path), str(width))
                    self.assertEqual(checked.returncode, 0, checked.stderr)

                open_resolved = resolve(dumps(program, format="json"))
                self.assertEqual(open_resolved.returncode, 0, open_resolved.stderr)
                instructions = json.loads(open_resolved.stdout)["instructions"]
                self.assertEqual(
                    [item for item in instructions if item["op"] == "query"],
                    [{"op": "query", "slot": "dj_function",
                      "arguments": [list(range(width)), [width]], "banks": []}],
                )
                if width > 3:
                    continue

                for expected_index in (0, 1 << (width - 1)):
                    with self.subTest(expected_index=expected_index):
                        oracle = Builder("dj_binding", {"address": Bits(width), "data": Bits(1)})
                        if expected_index:
                            oracle.xor(oracle["address"][width - 1], oracle["data"])
                        bound = bind(program, {"dj_function": oracle.finish()})
                        self.assertFalse(unresolved(bound))
                        state = simulate(bound)
                        self.assertEqual({key[0] for key in state.amplitudes}, {expected_index})
                        bound_resolved = resolve(dumps(bound, format="json"))
                        self.assertEqual(bound_resolved.returncode, 0, bound_resolved.stderr)
                        self.assertNotIn('"query"', bound_resolved.stdout)


class ScopedResolutionChecks(unittest.TestCase):
    def test_relative_frames_and_forwarded_banks(self) -> None:
        leaf = Builder("phase_lookup", {"addr": Bits(1)}, {"table": QRAM(1, 1)})
        tmp = leaf.local("tmp", Bits(1))
        flag = leaf.local("flag", Bits(1))
        leaf.qram("table", leaf["addr"], tmp)
        leaf.swap(tmp, flag)
        leaf.gate("phase", flag, math.pi / 2)
        leaf.swap(tmp, flag)
        leaf.qram("table", leaf["addr"], tmp)

        forward = Builder("forward", {"word": Bits(1)}, {"formal": QRAM(1, 1)})
        nested_tmp = forward.local("tmp", Bits(1))
        forward.xor(forward["word"], nested_tmp)
        forward.call(leaf.finish(), addr=nested_tmp, resources={"table": "formal"})
        forward.xor(forward["word"], nested_tmp)
        forwarded = forward.finish()

        entry = Builder("entry", {"index": Bits(2), "guard": Bits(1)},
                        {"left": QRAM(1, 1), "right": QRAM(1, 1)})
        workspace = entry.local("tmp", Bits(1))
        with entry.repeat(2):
            entry.x(workspace)
        entry.h(entry["index"])
        entry.h(entry["guard"])
        with entry.control(entry["guard"]):
            with entry.adjoint():
                entry.call(forwarded, word=entry["index"][1], resources={"formal": "left"})
            entry.call(forwarded, word=entry["index"][0], resources={"formal": "right"})
        program = entry.finish().program()
        resolved = resolve(dumps(program, format="json"))
        self.assertEqual(resolved.returncode, 0, resolved.stderr)
        report = json.loads(resolved.stdout)
        self.assertEqual(report["mode"], "scoped")
        self.assertEqual(report["wire_count"], 3)
        self.assertEqual(report["peak_local_wires"], 4)
        modules = {module["name"]: module for module in report["modules"]}
        self.assertEqual(list(modules), ["phase_lookup", "forward", "entry"])
        self.assertEqual(modules["entry"]["instructions"][:2], [{"op": "x", "wires": [3]}] * 2)
        calls = modules["entry"]["instructions"][-2:]
        self.assertEqual(calls, [
            {"op": "control", "wires": [2], "value": 1, "instruction": {
                "op": "adjoint", "instruction": {
                    "op": "query", "slot": "forward", "arguments": [[1]], "banks": ["left"],
                },
            }},
            {"op": "control", "wires": [2], "value": 1, "instruction": {
                "op": "query", "slot": "forward", "arguments": [[0]], "banks": ["right"],
            }},
        ])
        self.assertEqual(modules["forward"]["instructions"][1],
                         {"op": "query", "slot": "phase_lookup",
                          "arguments": [[1]], "banks": ["formal"]})
        phase = modules["phase_lookup"]["instructions"][4]
        self.assertEqual(phase["wires"], [2])
        self.assertEqual(phase["instruction"]["op"], "gphase")
        self.assertEqual(
            [(gate["source"], gate["target"])
             for gate in modules["phase_lookup"]["instructions"][1:4]],
            [([1], [2]), ([2], [1]), ([1], [2])],
        )

        memory = {"left": [0, 1], "right": [1, 0]}
        amplitudes = simulate(program, memory=memory).amplitudes
        self.assertEqual(len(amplitudes), 8)
        for (index, guard), amplitude in amplitudes.items():
            turns = guard * (memory["right"][index & 1] - memory["left"][index >> 1])
            self.assertAlmostEqual(amplitude, cmath.exp(1j * turns * math.pi / 2) / math.sqrt(8))

    def test_resolution_does_not_discharge_workspace_cleanup(self) -> None:
        entry = Builder("dirty", {"public": Bits(1)})
        entry.x(entry.local("tmp", Bits(1)))
        program = entry.finish().program()
        resolved = resolve(dumps(program, format="json"))
        self.assertEqual(resolved.returncode, 0, resolved.stderr)
        self.assertEqual(json.loads(resolved.stdout)["peak_local_wires"], 1)
        with self.assertRaisesRegex(ValidationError, "local register not restored to zero"):
            simulate(program)


class VerificationChecks(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.path = Path(directory.name)
        self.width = 3
        self.program = deutsch_jozsa(abstract_database("dj_function", self.width, 1)).program()
        self.original = self.save("python.open.json", dumps(self.program, format="json"))

    def save(self, name: str, text: str) -> str:
        path = self.path / name
        path.write_text(text, encoding="utf-8")
        return str(path)

    def checked_bound(self, program, memory=None):
        bound_path = self.save("python.bound.json", dumps(program, format="json"))
        arguments = ["verify-bound", DJ_THEOREM, self.original, bound_path, str(self.width)]
        if memory is not None:
            arguments.append(self.save("memory.json", json.dumps(memory)))
        return command(*arguments)

    def assert_ledger(self, report, program) -> None:
        measured = estimate_resources(program).to_dict()
        expected = {key: measured[key] for key in ("qubits", "gate_total", "qram_total")}
        expected.update({gate: measured["atoms"].get(gate, 0) for gate in ("h", "x", "cz")})
        self.assertEqual(report["resources"], expected)
        self.assertEqual(report["logical_oracle_calls"], 1)

    def test_python_open_and_concrete_gate_bindings(self) -> None:
        checked = command("verify", DJ_THEOREM, self.original, str(self.width))
        self.assertEqual(checked.returncode, 0, checked.stderr)
        self.assertEqual(json.loads(checked.stdout)["mode"], "open")
        for flavor, expected in (("zero", 0), ("one", 0), ("second_bit", 2)):
            with self.subTest(flavor=flavor):
                oracle = Builder("gate_oracle", {"address": Bits(self.width), "data": Bits(1)})
                if flavor == "one":
                    oracle.x(oracle["data"])
                elif flavor == "second_bit":
                    oracle.xor(oracle["address"][1], oracle["data"])
                bound = bind(self.program, {"dj_function": oracle.finish()})
                result = self.checked_bound(bound)
                self.assertEqual(result.returncode, 0, result.stderr)
                report = json.loads(result.stdout)
                self.assertEqual(report["promise"], "balanced" if expected else "constant")
                self.assertEqual(report["readout"], "nonzero" if expected else "zero")
                self.assert_ledger(report, bound)
                self.assertEqual({key[0] for key in simulate(bound).amplitudes}, {expected})

    def test_captured_dense_qram_and_promise_failure(self) -> None:
        oracle = Builder("table_oracle", {"address": Bits(self.width), "data": Bits(1)},
                         {"local_bank": QRAM(self.width, 1)})
        oracle.qram("local_bank", oracle["address"], oracle["data"])
        bound = bind(self.program, {"dj_function": Binding(oracle.finish(), {"local_bank": "truth"})})
        values = [0, 1, 0, 0, 1, 1, 1, 0]
        memory = {"truth": values}
        result = self.checked_bound(bound, memory)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["promise"], "balanced")
        self.assertEqual(report["qram_banks"], ["truth"])
        self.assert_ledger(report, bound)
        self.assertTrue(all(key[0] for key in simulate(bound, memory=memory).amplitudes))
        constant = self.checked_bound(bound, {"truth": [1] * len(values)})
        self.assertEqual(constant.returncode, 0, constant.stderr)
        self.assertEqual(json.loads(constant.stdout)["readout"], "zero")
        for tampered, message in (
            ({"truth": [1] + values[1:]}, "neither constant nor balanced"),
            ({"truth": values[:-1]}, "must supply exactly"),
            ({"truth": [2] + values[1:]}, "outside the one-bit data range"),
        ):
            with self.subTest(tampered=tampered):
                invalid = self.checked_bound(bound, tampered)
                self.assertNotEqual(invalid.returncode, 0)
                self.assertIn(message, invalid.stderr)

    def test_wide_python_binding_does_not_enumerate_addresses(self) -> None:
        self.width = 65
        self.program = deutsch_jozsa(abstract_database("dj_function", self.width, 1)).program()
        self.original = self.save("wide.open.json", dumps(self.program, format="json"))
        oracle = Builder("wide_oracle", {"address": Bits(self.width), "data": Bits(1)})
        oracle.xor(oracle["address"][64], oracle["data"])
        bound = bind(self.program, {"dj_function": oracle.finish()})
        result = self.checked_bound(bound)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["promise"], "balanced")
        self.assert_ledger(report, bound)

    def test_wrong_forwarding_and_non_xor_oracle_are_rejected(self) -> None:
        bad = json.loads(dumps(self.program, format="json"))
        entry = next(m for m in bad["modules"] if m["name"] == bad["entry"])
        view = entry["body"][3]["arguments"][0]
        first = view["parts"][0]
        view["parts"] = [dict(first, start=1, width=self.width - 1), dict(first, width=1)]
        path = self.save("wrong-order.json", json.dumps(bad))
        wrong_view = command("verify", DJ_THEOREM, path, str(self.width))
        self.assertNotEqual(wrong_view.returncode, 0)
        self.assertIn("oracle forwarding", wrong_view.stderr)

        projection = Builder("projection", {"address": Bits(self.width), "data": Bits(1)})
        projection.xor(projection["address"][0], projection["data"])
        bound = bind(self.program, {"dj_function": projection.finish()})
        bad = json.loads(dumps(bound, format="json"))
        wrapper = next(m for m in bad["modules"] if m["name"] == "dj_function")
        view = wrapper["body"][0]["arguments"][0]
        first = view["parts"][0]
        view["parts"] = [dict(first, start=1, width=self.width - 1), dict(first, width=1)]
        path = self.save("wrong-wrapper.json", json.dumps(bad))
        result = command("verify-bound", DJ_THEOREM, self.original, path, str(self.width))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("bound wrapper must forward", result.stderr)

        oracle = Builder("bad_oracle", {"address": Bits(self.width), "data": Bits(1)})
        oracle.h(oracle["data"])
        bound = bind(self.program, {"dj_function": oracle.finish()})
        wrong_behavior = self.checked_bound(bound)
        self.assertNotEqual(wrong_behavior.returncode, 0)
        self.assertIn("Unsupported oracle implementation", wrong_behavior.stderr)


class ForwardingChecks(unittest.TestCase):
    def test_qram_bank_alias_and_cross_register_slice(self) -> None:
        bank_type = QRAM(2, 1)
        leaf = Builder("reader", {"address": Bits(3), "data": Bits(1)},
                       {"primary": bank_type, "secondary": bank_type})
        leaf.qram("primary", leaf["address"][1:3], leaf["data"])
        leaf.qram("secondary", leaf["address"][0:2], leaf["data"])
        middle = Builder("middle", {"packed": Bits(3), "target": Bits(1)}, {"local": bank_type})
        middle.call(leaf.finish(), address=middle["packed"], data=middle["target"],
                    resources={"primary": "local", "secondary": "local"})
        entry = Builder("main", {"top": Bits(2), "bottom": Bits(2), "data": Bits(1)},
                        {"snapshot": bank_type})
        entry.call(middle.finish(), packed=fuse(entry["top"][1], entry["bottom"][0], entry["top"][0]),
                   target=entry["data"], resources={"local": "snapshot"})
        program = entry.finish().program()
        canonical = dumps(program, format="json")

        resolved = resolve(canonical)
        self.assertEqual(resolved.returncode, 0, resolved.stderr)
        self.assertEqual(json.loads(resolved.stdout), {
            "wire_count": 5,
            "instructions": [
                {"op": "load", "bank": "snapshot", "address": [2, 0], "data": [4]},
                {"op": "load", "bank": "snapshot", "address": [1, 2], "data": [4]},
            ],
        })
        state = simulate(program, memory={"snapshot": [0, 1, 0, 0]},
                         initial={"bottom": 1, "data": 1})
        self.assertEqual(state.amplitudes, {(0, 1, 0): 1 + 0j})

        invalid = json.loads(canonical)
        call = next(m for m in invalid["modules"] if m["name"] == invalid["entry"])["body"][0]
        call["arguments"][1]["parts"] = [call["arguments"][0]["parts"][0]]
        result = resolve(json.dumps(invalid))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Call arguments overlap", result.stderr)

        invalid = json.loads(canonical)
        reader = next(m for m in invalid["modules"] if m["name"] == "reader")
        reader["resources"][0]["type"]["address_width"] = 1
        result = resolve(json.dumps(invalid))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("QRAM type mismatch", result.stderr)


class SourceLinkChecks(unittest.TestCase):
    def test_scoped_binding_preserves_ordered_arguments_and_captured_bank(self) -> None:
        bank = QRAM(2, 1)
        ports = {"address": Bits(2), "data": Bits(1)}
        slot = declare("scoped_lookup", ports, resources={"original": bank})
        leaf = Builder("scoped_leaf", ports, {"original": bank, "extra": bank})
        work = leaf.local("work", Bits(1))
        leaf.qram("original", leaf["address"], work)
        leaf.gate("phase", work, 0.625)
        leaf.qram("original", leaf["address"], work)
        leaf.qram("extra", leaf["address"], leaf["data"])

        middle = Builder("scoped_forward", ports, {"formal": bank})
        scratch = middle.local("work", Bits(1))
        with middle.repeat(2):
            middle.x(scratch)
        middle.call(slot, address=middle["address"], data=middle["data"],
                    resources={"original": "formal"})
        forward = middle.finish()
        entry = Builder("scoped_entry", {"layout": Bits(4), "data": Bits(1), "guard": Bits(1)},
                        {"left": bank, "right": bank})
        entry.h(entry["layout"])
        entry.h(entry["guard"])
        with entry.control(entry["guard"]):
            with entry.adjoint():
                entry.call(forward, address=fuse(entry["layout"][3], entry["layout"][0]),
                           data=entry["data"], resources={"formal": "left"})
            entry.call(forward, address=fuse(entry["layout"][0], entry["layout"][2]),
                       data=entry["data"], resources={"formal": "right"})
        source = entry.finish().program()
        bound = bind(source, {"scoped_lookup": Binding(leaf.finish(), {"extra": "tables"})})
        serialized = dumps(bound, format="json")
        capture = {"name": "tables", "address_width": 2, "data_width": 1}
        approved = {
            "scoped_entry": {"scoped_forward": [0, capture]},
            # The pinned binder's lexical alias in the forwarding module.
            "scoped_forward": {"scoped_lookup": [
                0, {**capture, "name": "capture_d98a034f5cb8a0e3"},
            ]},
        }

        with tempfile.TemporaryDirectory() as directory:
            open_path = Path(directory) / "open.json"
            bound_path = Path(directory) / "bound.json"
            plan_path = Path(directory) / "plan.json"
            open_path.write_text(dumps(source, format="json"), encoding="utf-8")

            def check(candidate: str, plan=None):
                bound_path.write_text(candidate, encoding="utf-8")
                args = ["check-scoped-link", str(open_path), str(bound_path)]
                if plan is not None:
                    plan_path.write_text(json.dumps(plan), encoding="utf-8")
                    args.append(str(plan_path))
                return command(*args)

            accepted = check(serialized, approved)
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            report = json.loads(accepted.stdout)
            self.assertEqual(report["mode"], "structural-scoped-link")
            self.assertEqual(report["wire_count"], 6)
            self.assertEqual(report["slots"], ["scoped_lookup"])
            abstract = {module["name"]: module for module in report["caller"]}
            concrete = {module["name"]: module for module in report["bound"]}
            self.assertIsNone(abstract["scoped_lookup"]["instructions"])
            self.assertEqual(concrete["scoped_leaf"]["local_wires"], 1)
            self.assertEqual(concrete["scoped_entry"]["peak_local_wires"], 2)
            first, second = abstract["scoped_entry"]["instructions"][-2:]
            self.assertEqual(first["instruction"]["instruction"]["arguments"], [[3, 0], [4]])
            self.assertEqual(first["instruction"]["instruction"]["banks"], ["left", "tables"])
            self.assertEqual(second["instruction"]["arguments"], [[0, 2], [4]])
            self.assertEqual(second["instruction"]["banks"], ["right", "tables"])

            self.assertNotEqual(check(serialized).returncode, 0)
            for label, expected in (
                ("quantum", "ordered actual"),
                ("bank", "ordered actual"),
                ("formal", "original bank"),
                ("workspace", "caller workspace"),
            ):
                with self.subTest(change=label):
                    altered = json.loads(serialized)
                    modules = {m["name"]: m for m in altered["modules"]}
                    control = modules["scoped_entry"]["body"][-1]
                    first_call = control["body"][0]["body"][0]
                    if label == "quantum":
                        first_call["arguments"][0]["parts"].reverse()
                    elif label == "bank":
                        first_call["resources"][0] = "right"
                    elif label == "formal":
                        modules["scoped_forward"]["resources"].reverse()
                    else:
                        private = modules["scoped_forward"]["locals"][0]
                        private["type"]["width"] = 2
                    rejected = check(json.dumps(altered), approved)
                    self.assertNotEqual(rejected.returncode, 0, rejected.stdout)
                    self.assertIn(expected, rejected.stderr)

        memory = {"left": [1, 0, 0, 1], "right": [1, 0, 1, 0], "tables": [0, 1, 1, 0]}
        amplitudes = simulate(bound, memory=memory).amplitudes
        self.assertEqual(len(amplitudes), 32)
        for (layout, data, guard), amplitude in amplitudes.items():
            left = ((layout >> 3) & 1) | ((layout & 1) << 1)
            right = (layout & 1) | (((layout >> 2) & 1) << 1)
            self.assertEqual(data, guard * (memory["tables"][left] ^ memory["tables"][right]))
            phase = guard * 0.625 * (memory["right"][right] - memory["left"][left])
            self.assertAlmostEqual(amplitude, cmath.exp(1j * phase) / math.sqrt(32))

    def test_controlled_adjoint_binding_with_distinct_bank_and_wire_actuals(self) -> None:
        bank = QRAM(2, 1)
        ports = {"address": Bits(2), "data": Bits(1), "enabled": Bits(1)}
        slot = declare("open_lookup", ports, resources={"original": bank})
        implementation = Builder("lookup_impl", ports, {"original": bank, "extra": bank})
        with implementation.control(implementation["enabled"], 1):
            implementation.global_phase(0.625)
        implementation.qram("original", implementation["address"], implementation["data"])
        with implementation.adjoint():
            implementation.qram("extra", implementation["address"], implementation["data"])

        middle = Builder("forward", ports, {"local": bank})
        middle.call(slot, address=middle["address"], data=middle["data"], enabled=middle["enabled"],
                    resources={"original": "local"})
        entry = Builder("main", {"layout": Bits(4), "data": Bits(1),
                                 "outer": Bits(1), "enabled": Bits(1)},
                        {"left": bank, "right": bank})
        forward = middle.finish()
        with entry.control(entry["outer"], 1):
            with entry.adjoint():
                entry.call(forward, address=fuse(entry["layout"][3], entry["layout"][0]),
                           data=entry["data"], enabled=entry["enabled"], resources={"local": "left"})
            entry.call(forward, address=fuse(entry["layout"][0], entry["layout"][2]),
                       data=entry["data"], enabled=entry["enabled"], resources={"local": "right"})
        source = entry.finish().program()
        bound = bind(source, {"open_lookup": Binding(implementation.finish(), {"extra": "tables"})})
        bound_json = dumps(bound, format="json")
        capture = {"name": "tables", "address_width": 2, "data_width": 1}

        with tempfile.TemporaryDirectory() as directory:
            open_path = Path(directory) / "open.json"
            bound_path = Path(directory) / "bound.json"
            plan_path = Path(directory) / "plan.json"
            open_path.write_text(dumps(source, format="json"), encoding="utf-8")

            def check(candidate: str, plan: dict | None = None):
                bound_path.write_text(candidate, encoding="utf-8")
                args = ["check-link", str(open_path), str(bound_path)]
                if plan is not None:
                    plan_path.write_text(json.dumps(plan), encoding="utf-8")
                    args.append(str(plan_path))
                return command(*args)

            approved = {"open_lookup": [0, capture]}
            accepted = check(bound_json, approved)
            self.assertEqual(accepted.returncode, 0, accepted.stderr)
            report = json.loads(accepted.stdout)
            self.assertEqual(report["wire_count"], 7)
            self.assertEqual(report["closed_instructions"], 6)
            self.assertEqual([item["call"] for item in report["implementations"]], [
                {"op": "query", "slot": "open_lookup", "arguments": [[3, 0], [4], [6]],
                 "banks": ["left", "tables"]},
                {"op": "query", "slot": "open_lookup", "arguments": [[0, 2], [4], [6]],
                 "banks": ["right", "tables"]},
            ])
            for item in report["implementations"]:
                phase, read, inverse_read = item["implementation"]
                self.assertEqual(phase["instruction"]["angle"], 0.625)
                self.assertEqual(read["bank"], item["call"]["banks"][0])
                self.assertEqual(inverse_read["instruction"]["bank"], "tables")

            missing = check(bound_json)
            self.assertNotEqual(missing.returncode, 0)
            self.assertIn("ordered wire or bank actuals", missing.stderr)
            dropped = check(bound_json, {"open_lookup": [capture]})
            self.assertNotEqual(dropped.returncode, 0)
            self.assertIn("forward every original bank", dropped.stderr)

            for mutation in ("wire order", "bank identity"):
                with self.subTest(mutation=mutation):
                    changed = json.loads(bound_json)
                    main = next(m for m in changed["modules"] if m["name"] == changed["entry"])
                    call = main["body"][0]["body"][0]["body"][0]
                    if mutation == "wire order":
                        call["arguments"][0]["parts"].reverse()
                    else:
                        call["resources"][0] = "right"
                    rejected = check(json.dumps(changed), approved)
                    self.assertNotEqual(rejected.returncode, 0)
                    self.assertIn("ordered wire or bank actuals", rejected.stderr)


if __name__ == "__main__":
    unittest.main()
