"""Cross-check the extended Lean resolver with Oracq's closed-program events."""

from decimal import Decimal
from functools import partial
import cmath
import json
from math import pi, sqrt
from pathlib import Path
import sys
import unittest

from oracq import Bits, Builder, QRAM, dumps, fuse, simulate
from oracq.algorithms.common.hamiltonian import taylor_hamiltonian
from oracq.algorithms.input_model.block_encoding import matrix_pauli_encoding
from oracq.algorithms.input_model.oracles import gate_state_prep
from oracq.algorithms.qode.lchs import QuadraturePlan, lchs_qode
from oracq.algorithms.qode.ode_models import HermitianParts, LinearODE
from oracq.infrastructure.execution import events
from oracq.infrastructure.ir import Call, Control, Load, Primitive, Program, Ref

from check_generated import resolve


FIXTURE = Path(__file__).resolve().parents[1] / "fixtures" / "lchs.noncommuting.json"


def wires(ref: Ref, offsets: dict[str, int]) -> list[int]:
    return [
        offsets[part.register] + index
        for part in ref.parts
        for index in range(part.start, part.start + part.width)
    ]


def expand_oracq(program: Program) -> list[tuple[dict, list[dict], bool]]:
    offsets = {}
    offset = 0
    for register in program.main.registers:
        offsets[register.name] = offset
        offset += register.type.width

    expanded = []
    for instruction, controls, inverse in events(program):
        guards = [{"wires": wires(ref, offsets), "value": value} for ref, value in controls]
        if isinstance(instruction, Primitive):
            atom = {"op": instruction.op}
            if instruction.angle is not None:
                atom["angle"] = Decimal(str(instruction.angle))
            if instruction.op == "xor":
                src, dst = instruction.operands
                atom.update(source=wires(src, offsets), target=wires(dst, offsets))
            elif instruction.operands:
                (ref,) = instruction.operands
                atom["wires"] = wires(ref, offsets)
                if instruction.op == "add_const":
                    atom["amount"] = instruction.value
        elif isinstance(instruction, Load):
            atom = {"op": "load", "bank": instruction.resource,
                    "address": wires(instruction.address, offsets),
                    "data": wires(instruction.data, offsets)}
        else:
            raise AssertionError(f"Unexpected Oracq event: {instruction}")
        expanded.append((atom, guards, inverse))
    return expanded


def flatten_resolved(instruction: dict) -> tuple[dict, list[dict], bool]:
    guards = []
    inverse = False
    while instruction["op"] in ("control", "adjoint"):
        if instruction["op"] == "control":
            guards.append({"wires": instruction["wires"], "value": instruction["value"]})
        else:
            inverse = not inverse
        instruction = instruction["instruction"]
    return instruction, guards, inverse


def lchs_preflight() -> Program:
    nodes = (-1.0, -0.5, 0.0, 0.5)
    weights = tuple(0.5 / (pi * (1 + k * k)) for k in nodes)
    plan = QuadraturePlan(nodes, weights, "cauchy_left_endpoint")
    parts = HermitianParts(matrix_pauli_encoding([[1.5, 0.0], [0.0, 0.5]]),
                           matrix_pauli_encoding([[0.0, 0.25], [0.25, 0.0]]))
    model = LinearODE(parts, gate_state_prep([1, 0]))
    solver = lchs_qode(model, 0.125, plan=plan,
                      hamiltonian_function=partial(taylor_hamiltonian, degree=2))
    return solver.operation.program()


def taylor_entry(node: float, row: int, column: int) -> complex:
    hamiltonian = ((1.5 * node, 0.25), (0.25, 0.5 * node))
    time = 0.125
    square = sum(hamiltonian[row][i] * hamiltonian[i][column] for i in range(2))
    return int(row == column) - 1j * time * hamiltonian[row][column] - time**2 / 2 * square


class ExtendedSemanticsChecks(unittest.TestCase):
    def assert_trace(self, program: Program) -> list[tuple[dict, list[dict], bool]]:
        result = resolve(dumps(program, format="json"))
        self.assertEqual(result.returncode, 0, result.stderr)
        output = json.loads(result.stdout, parse_float=Decimal)
        self.assertEqual(output["wire_count"], sum(reg.type.width for reg in program.main.registers))
        trace = [flatten_resolved(instruction) for instruction in output["instructions"]]
        self.assertEqual(trace, expand_oracq(program))
        return trace

    def test_actual_noncommuting_lchs(self) -> None:
        program = lchs_preflight()
        trace = self.assert_trace(program)
        self.assertEqual(len(program.modules), 32)
        self.assertEqual(set(atom["op"] for atom, _, _ in trace), {"gphase", "ry", "z", "x"})
        self.assertTrue(any(atom["op"] == "gphase" and atom["angle"] and guards
                            for atom, guards, _ in trace))
        self.assertTrue(any(inverse and atom["op"] == "ry" for atom, _, inverse in trace))
        self.assertTrue(any(len(guards) > 1 for _, guards, _ in trace))

    def test_first_taylor_branch_success_block(self) -> None:
        program = lchs_preflight()
        outer_call = program.main.body[1]
        self.assertIsInstance(outer_call, Call)
        select = program.module_map[outer_call.module].body[1]
        self.assertIsInstance(select, Control)
        self.assertEqual(select.value, 0)
        branch_call = select.body[1]
        self.assertIsInstance(branch_call, Call)
        branch = Program(branch_call.module, program.modules)
        self.assert_trace(branch)
        alpha = dict(branch.main.attributes)["be_alpha"]
        self.assertEqual(alpha, 2545 / 2048)
        for col in range(2):
            amplitudes = simulate(branch, initial={"target": col}).amplitudes
            for row in range(2):
                self.assertAlmostEqual(
                    alpha * amplitudes.get((row, 0), 0), taylor_entry(-1.0, row, col), places=12
                )

    def test_full_lchs_success_amplitude(self) -> None:
        program = lchs_preflight()
        alpha = dict(program.main.attributes)["evolution_alpha"]
        for col in range(2):
            amplitudes = simulate(program, initial={"target": col}).amplitudes
            for row in range(2):
                expected = sum(
                    0.5 / (pi * (1 + k**2)) * taylor_entry(k, row, col)
                    for k in (-1.0, -0.5, 0.0, 0.5)
                )
                self.assertAlmostEqual(alpha * amplitudes.get((row, 0), 0), expected, places=12)

    def test_guarded_phase_is_relative_on_a_superposition(self) -> None:
        program = Builder("controlled_phase", {"control": Bits(1)})
        program.h(program["control"])
        with program.control(program["control"], 0):
            program.global_phase(0.625)
        program = program.finish().program()
        trace = self.assert_trace(program)
        self.assertEqual(trace[1], ({"op": "gphase", "angle": Decimal("0.625")},
                                    [{"wires": [0], "value": 0}], False))
        amplitudes = simulate(program).amplitudes
        self.assertAlmostEqual(amplitudes[(0,)], cmath.exp(0.625j) / sqrt(2))
        self.assertAlmostEqual(amplitudes[(1,)], 1 / sqrt(2))

    def test_adjoint_reversal_and_multispan_guard(self) -> None:
        leaf = Builder("rotate", {"target": Bits(1)})
        leaf.ry(leaf["target"], 0.125)
        leaf.z(leaf["target"])
        leaf = leaf.finish()
        entry = Builder("guarded_rotation", {"low": Bits(1), "high": Bits(1), "target": Bits(1)})
        with entry.control(fuse(entry["high"], entry["low"]), 1):
            with entry.adjoint():
                entry.call(leaf, target=entry["target"])
                with entry.adjoint():
                    entry.global_phase(-0.75)
        trace = self.assert_trace(entry.finish().program())
        guard = [{"wires": [1, 0], "value": 1}]
        self.assertEqual(trace, [
            ({"op": "gphase", "angle": Decimal("-0.75")}, guard, False),
            ({"op": "z", "wires": [2]}, guard, True),
            ({"op": "ry", "angle": Decimal("0.125"), "wires": [2]}, guard, True),
        ])

    def test_control_can_read_qram_address_but_never_modify_it(self) -> None:
        entry = Builder("read_guard", {"address": Bits(1), "target": Bits(1)}, {"table": QRAM(1, 1)})
        with entry.control(entry["address"]):
            entry.qram("table", entry["address"], entry["target"])
        program = entry.finish().program()
        self.assert_trace(program)

        malformed = json.loads(dumps(program, format="json"))
        module = next(item for item in malformed["modules"] if item["name"] == malformed["entry"])
        control = module["body"][0]
        control["register"] = control["body"][0]["data"]
        result = resolve(json.dumps(malformed))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("protected control wire", result.stderr)

    def test_call_capabilities_are_checked_under_control_and_adjoint(self) -> None:
        leaf = Builder("rotate", {"target": Bits(1)})
        leaf.ry(leaf["target"], 0.125)
        entry = Builder("with_context", {"control": Bits(1), "target": Bits(1)})
        with entry.control(entry["control"]):
            with entry.adjoint():
                entry.call(leaf.finish(), target=entry["target"])
        program = entry.finish().program()
        self.assert_trace(program)
        for name in ("supports_controlled", "supports_adjoint"):
            with self.subTest(capability=name):
                malformed = json.loads(dumps(program, format="json"))
                callee = next(module for module in malformed["modules"] if module["name"] == "rotate")
                callee["attributes"] = [[name, False]]
                result = resolve(json.dumps(malformed))
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(f"lacks {name}", result.stderr)


if __name__ == "__main__":
    artifact = json.loads(dumps(lchs_preflight(), format="json"))
    fields = {key: value for key, value in artifact.items() if key != "modules"}
    header = json.dumps(fields, separators=(",", ":"))
    modules = ",\n".join(json.dumps(module, separators=(",", ":")) for module in artifact["modules"])
    payload = header[:-1] + ',\n"modules":[\n' + modules + "\n]}\n"
    if sys.argv[1:] == ["--update-fixture"]:
        FIXTURE.write_text(payload, encoding="utf-8")
    else:
        if FIXTURE.read_text(encoding="utf-8") != payload:
            raise SystemExit("Static LCHS fixture differs from the pinned Oracq generator")
        unittest.main()
