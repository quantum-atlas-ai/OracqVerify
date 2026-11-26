"""Generate and certify three component replacements in serialized Oracq RIR."""

import argparse
import json
from functools import partial
from math import acos, pi
from pathlib import Path
import subprocess
import tempfile

from oracq import Binding, Bits, Builder, QRAM, bind, declare, dumps, loads, unresolved
from oracq.algorithms.common.hamiltonian import taylor_hamiltonian
from oracq.algorithms.common.qsvt import fixed_point_search
from oracq.algorithms.common.search import amplify_success
from oracq.algorithms.input_model.block_encoding import lcu, matrix_pauli_encoding
from oracq.algorithms.input_model.operators import block_encoding
from oracq.algorithms.input_model.oracles import StateOracle, gate_state_prep
from oracq.algorithms.qode.lchs import QuadraturePlan, lchs_qode
from oracq.algorithms.qode.ode_models import HermitianParts, LinearODE
from oracq.infrastructure.execution import events
from oracq.infrastructure.ir import Primitive

ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / ".lake/build/bin/oracq-verify"


def save(directory, name, program):
    path = directory / (name + ".json")
    path.write_text(dumps(program, format="json"), encoding="utf-8")
    return loads(path.read_text(encoding="utf-8"))


def sparse(directory):
    registers = {"target": Bits(2), "signal": Bits(1)}
    flag = declare("sparse_entry_flag", registers)
    b = Builder("sparse_block", registers, attributes={"be_alpha": 1})
    b.call(flag, target=b["target"], signal=b["signal"])
    b.x(b["target"][0])
    original = save(directory, "sparse-open", b.finish().program())

    gate = Builder("sparse_flag_gate", registers)
    gate.xor(gate["target"][1], gate["signal"])
    qram = Builder("sparse_flag_qram", registers, {"lookup": QRAM(2, 1)})
    qram.qram("lookup", qram["target"], qram["signal"])
    save(directory, "sparse-gate", bind(original, {"sparse_entry_flag": gate.finish()}))
    save(directory, "sparse-qram", bind(
        original, {"sparse_entry_flag": Binding(qram.finish(), {"lookup": "edge_flags"})}))
    (directory / "sparse-image.json").write_text('{"edge_flags":[0,0,1,1]}\n', encoding="utf-8")


def lchs(directory):
    nodes = (-1.0, -0.5, 0.0, 0.5)
    plan = QuadraturePlan(nodes, tuple(0.5 / (pi * (1 + k * k)) for k in nodes),
                          "cauchy_left_endpoint")
    parts = HermitianParts(matrix_pauli_encoding([[1.5, 0.0], [0.0, 0.5]]),
                           matrix_pauli_encoding([[0.0, 0.25], [0.25, 0.0]]))
    model = LinearODE(parts, gate_state_prep([1, 0]))
    node_by_module = {lcu([(1, parts.h), (k, parts.hermitian)]).operation.module.name: k
                      for k in nodes}

    def product_formula(encoding, time):
        k = node_by_module[encoding.operation.module.name]
        b = Builder(f"product_formula_{encoding.operation.module.name}",
                    {"target": Bits(1), "signal": Bits(0)})
        target = b["target"]
        # K = k I + (k/2) Z + X/4. Encode each Rz as a global and conditional phase.
        b.global_phase(-k * time)
        b.global_phase(-k * time / 2)
        with b.control(target):
            b.global_phase(k * time)
        b.h(target)
        b.global_phase(-time / 4)
        with b.control(target):
            b.global_phase(time / 2)
        b.h(target)
        return block_encoding(b.finish())

    backends = (("taylor", partial(taylor_hamiltonian, degree=2)), ("product", product_formula))
    for name, backend in backends:
        solver = lchs_qode(model, 0.125, plan=plan, hamiltonian_function=backend)
        save(directory, f"lchs-{name}", solver.operation.program())

    time = 0.125
    signal_width = 7
    common_scale = 2.0
    interface = {"target": Bits(1), "signal": Bits(signal_width)}
    hamiltonians = {node: lcu([(1, parts.h), (node, parts.hermitian)]) for node in nodes}
    slots = {node: block_encoding(declare(f"lchs_node_{i}", interface, paradigm="block_encoding"), common_scale)
             for i, node in enumerate(nodes)}

    def declare_branch(encoding, _time):
        return slots[node_by_module[encoding.operation.module.name]]

    assembler = lchs_qode(model, time, plan=plan, hamiltonian_function=declare_branch)
    original = save(directory, "lchs-open", assembler.operation.program())
    assert {item.name for item in unresolved(original)} == {slot.operation.module.name for slot in slots.values()}

    choices = {}
    for name, backend in backends:
        bindings = {}
        for index, node in enumerate(nodes):
            branch = backend(hamiltonians[node], time)
            assert branch.signal_qubits < signal_width and 0 < branch.alpha <= common_scale
            adapter = Builder(f"lchs_{name}_node_{index}", interface)
            signal = adapter["signal"]
            adapter.call(branch.operation, target=adapter["target"], signal=signal[:branch.signal_qubits])
            # The extra signal bit contributes alpha/2 to the zero-signal corner.
            adapter.ry(signal[signal_width - 1], 2 * acos(branch.alpha / common_scale))
            slot_name = slots[node].operation.module.name
            bindings[slot_name] = block_encoding(adapter.finish(), common_scale).operation
        choices[name] = bindings
        bound = bind(original, bindings)
        assert not unresolved(bound)
        save(directory, f"lchs-bound-{name}", bound)
    central = slots[0.0].operation.module.name
    mixed = {**choices["product"], central: choices["taylor"][central]}
    save(directory, "lchs-bound-mixed", bind(original, mixed))
    return original, {**choices, "mixed": mixed}


def amplification(directory):
    registers = {"target": Bits(1), "signal": Bits(1)}
    prep = Builder("amplification_input", registers)
    prep.ry(prep["signal"], 2.0)
    encoding = block_encoding(prep.finish())
    save(directory, "amp-input", encoding.operation.program())

    slot = declare("amplifier", registers)
    b = Builder("run_amplifier", registers)
    b.call(slot, target=b["target"], signal=b["signal"])
    original = save(directory, "amp-open", b.finish().program())

    standard = amplify_success(StateOracle(encoding.operation), iterations=1).operation
    fixed = fixed_point_search(encoding, delta=0.2, degree=5).operation
    for name, operation, queries in (("standard", standard, 3), ("fixed", fixed, 5),
                                      ("unamplified", encoding.operation, 1)):
        bound = save(directory, f"amp-{name}", bind(original, {"amplifier": operation}))
        assert sum(isinstance(step, Primitive) and step.op == "ry"
                   for step, _, _ in events(bound)) == queries


def run(directory, *args, reject=None):
    result = subprocess.run([CLI, "check-replacement", *args], cwd=directory,
                            text=True, capture_output=True)
    if reject is not None:
        assert result.returncode != 0 and reject in result.stderr, result
        return None
    assert result.returncode == 0, result.stderr
    return json.loads(result.stdout)


def check_linked_lchs(directory):
    source = directory / "lchs-open.json"

    def command(*candidates, original=source):
        return subprocess.run(
            [CLI, "check-lchs-link", original, *candidates], text=True, capture_output=True,
        )

    candidates = [directory / f"lchs-bound-{name}.json" for name in ("taylor", "product", "mixed")]
    result = command(*candidates)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report["verified"] and report["mode"] == "lchs-link"
    assert report["selector_certificates"] == 1
    assert len(set(report["shared_slots"])) == 4
    expected = {"wires": 10, "quadrature_error": "1/50", "assembly_error": "1/10000000000"}
    assert report["bindings"] == [expected] * 3, report

    def mutate(name, edit, diagnostic):
        program = json.loads(candidates[1].read_text(encoding="utf-8"))
        modules = {module["name"]: module for module in program["modules"]}
        lcu = modules[modules[program["entry"]]["body"][1]["module"]]
        edit(modules, lcu)
        path = directory / f"lchs-link-wrong-{name}.json"
        path.write_text(json.dumps(program), encoding="utf-8")
        result = command(path)
        assert result.returncode != 0 and diagnostic in result.stderr, result.stderr

    def change_selector(modules, lcu):
        prepare = modules[lcu["body"][0]["module"]]
        prepare["body"][0]["angle"] += 0.000001

    def swap_slot_implementations(modules, lcu):
        first, second = [modules[select["body"][1]["module"]] for select in lcu["body"][1:3]]
        first["body"], second["body"] = second["body"], first["body"]

    def change_adapter(modules, lcu):
        first = modules[lcu["body"][1]["body"][1]["module"]]
        adapter = modules[first["body"][0]["module"]]
        adapter["body"][-1]["angle"] += 0.25

    mutate("selector", change_selector, "Binding changed")
    mutate("slots", swap_slot_implementations, "Hamiltonian approximation budget")
    mutate("adapter", change_adapter, "Hamiltonian approximation budget")

    # Change both inputs consistently. Binding comparison alone accepts the changed
    # caller, but its nonidentity entry preparation disagrees with the LCU contract.
    changed = []
    for original in (source, candidates[1]):
        program = json.loads(original.read_text(encoding="utf-8"))
        modules = {module["name"]: module for module in program["modules"]}
        initial = modules[program["entry"]]["body"][0]["module"]
        modules[initial]["body"][0]["angle"] = 0.125
        target = directory / f"wrong-initial-{original.name}"
        target.write_text(json.dumps(program), encoding="utf-8")
        changed.append(target)
    rejected = command(changed[1], original=changed[0])
    assert rejected.returncode != 0 and "gate word differs" in rejected.stderr, rejected.stderr
    print("LCHS: structural assembly and one selector certificate for Taylor, product, and mixed bindings")


def check(directory):
    for variant in ("gate", "qram"):
        report = run(directory, "sparse", variant, "sparse-open.json", f"sparse-{variant}.json",
                     "sparse-image.json")
        assert report["mode"] == "sparse-block" and report["operator_error"] == "0", report
    (directory / "wrong-image.json").write_text('{"edge_flags":[0,1,1,1]}\n', encoding="utf-8")
    run(directory, "sparse", "qram", "sparse-open.json", "sparse-qram.json",
        "wrong-image.json", reject="permutation")

    report = run(directory, "lchs", "lchs-taylor.json", "lchs-product.json")
    assert report == {"mode": "lchs", "operator_error": "47/100",
                      "backend_discrepancy": "1/1000", "baseline_wires": 9,
                      "candidate_wires": 3}, report
    mutated = json.loads((directory / "lchs-product.json").read_text(encoding="utf-8"))
    entry = next(module for module in mutated["modules"] if module["name"] == mutated["entry"])
    entry["attributes"] = [[key, 0.1 if key == "evolution_alpha" else value]
                           for key, value in entry["attributes"]]
    (directory / "wrong-scale.json").write_text(json.dumps(mutated), encoding="utf-8")
    run(directory, "lchs", "wrong-scale.json", "lchs-product.json", reject="scaled success block")

    for variant, width in (("taylor", 9), ("product", 3)):
        source = directory / f"lchs-{variant}.json"
        result = subprocess.run([CLI, "check-lchs-components", source], text=True,
                                capture_output=True, check=False)
        assert result.returncode == 0, result.stderr
        assert json.loads(result.stdout) == {
            "verified": True, "mode": "lchs-components", "nodes": 4,
            "branch_error": "3/200", "assembly_error": "1/10000000000",
            "quadrature_error": "1/50", "wires": width,
        }

    mutated = json.loads((directory / "lchs-product.json").read_text(encoding="utf-8"))
    root = next(module for module in mutated["modules"] if module["name"] == mutated["entry"])
    wrong_nodes = directory / "wrong-nodes.json"
    attr = next(pair for pair in root["attributes"] if pair[0] == "quadrature_nodes")
    original_nodes = attr[1]
    attr[1] = "[-0.5, -1.0, 0.0, 0.5]"
    wrong_nodes.write_text(json.dumps(mutated), encoding="utf-8")
    result = subprocess.run([CLI, "check-lchs-components", wrong_nodes], text=True, capture_output=True)
    assert result.returncode != 0 and "quadrature node order" in result.stderr, result.stderr
    attr[1] = original_nodes
    outer = next(module for module in mutated["modules"] if module["name"] == root["body"][1]["module"])
    first = outer["body"][1]["body"][1]
    selected = next(module for module in mutated["modules"] if module["name"] == first["module"])
    scale = next(pair for pair in selected["attributes"] if pair[0] == "be_alpha")
    scale[1] = 0.99
    wrong_branch = directory / "wrong-branch-scale.json"
    wrong_branch.write_text(json.dumps(mutated), encoding="utf-8")
    result = subprocess.run([CLI, "check-lchs-components", wrong_branch], text=True, capture_output=True)
    assert result.returncode != 0 and "Hamiltonian approximation" in result.stderr, result.stderr

    scale[1] = 1.0
    prepare = next(module for module in mutated["modules"] if module["name"] == outer["body"][0]["module"])
    assert prepare["body"][0]["op"] == "ry"
    prepare["body"][0]["angle"] += 0.000001
    wrong_weight = directory / "wrong-weight.json"
    wrong_weight.write_text(json.dumps(mutated), encoding="utf-8")
    result = subprocess.run([CLI, "check-lchs-components", wrong_weight], text=True, capture_output=True)
    assert result.returncode != 0 and "selector probabilities" in result.stderr, result.stderr

    for variant in ("standard", "fixed"):
        report = run(directory, "amplification", "amp-open.json", f"amp-{variant}.json", "amp-input.json")
        assert report["mode"] == "amplification" and report["success_lower"] == "97/100", report
    run(directory, "amplification", "amp-open.json", "amp-unamplified.json", "amp-input.json",
        reject="success probability")
    print("Replacements: exact sparse block, two LCHS backends, two certified amplifiers")


def artifacts(directory):
    sparse(directory)
    lchs(directory)
    amplification(directory)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, metavar="DIR")
    args = parser.parse_args()
    if args.export is not None:
        args.export.mkdir(parents=True, exist_ok=True)
        artifacts(args.export)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            artifacts(directory)
            check(directory)
            check_linked_lchs(directory)
