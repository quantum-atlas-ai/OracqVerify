"""Build and test the width-parameterized Grover and coupled LCHS examples."""

import argparse
import json
from math import asin, isclose, sin, sqrt
from pathlib import Path
import subprocess
import tempfile
from time import perf_counter

from oracq import Binding, Bits, Builder, QRAM, bind, declare, dumps, loads, simulate
from oracq.infrastructure.builder import Operation

from check_replacements import CLI, lchs, save


def grover_artifacts(directory, width, iterations, with_qram=True):
    slot = declare("grover_wide_mark", {"target": Bits(width)}, paradigm="phase_oracle")
    caller = Builder("grover_wide", {"target": Bits(width)})
    target = caller["target"]
    caller.h(target)
    with caller.repeat(iterations):
        caller.call(slot, target=target)
        caller.h(target)
        caller.z(target[0])
        for i in range(1, width):
            with caller.control(target[:i], 0):
                caller.z(target[i])
        caller.h(target)
    source = save(directory, "open", caller.finish().program())

    gate = Builder("wide_mark_gate", {"target": Bits(width)}, attributes={"oracle_paradigm": "phase_oracle"})
    if width == 1:
        gate.z(gate["target"])
    else:
        with gate.control(gate["target"][:width - 1], 0):
            gate.z(gate["target"][width - 1])
    save(directory, "gate", bind(source, {slot.module.name: gate.finish()}))

    memory = {}
    if with_qram:
        qram = Builder("wide_mark_qram", {"target": Bits(width)}, {"lookup": QRAM(width, 1)},
                       attributes={"oracle_paradigm": "phase_oracle"})
        flag = qram.local("flag", Bits(1))
        qram.qram("lookup", qram["target"], flag)
        qram.z(flag)
        qram.qram("lookup", qram["target"], flag)
        save(directory, "qram", bind(source, {slot.module.name: Binding(qram.finish(), {"lookup": "marks"})}))
        mark = 1 << (width - 1)
        memory["marks"] = [int(i == mark) for i in range(1 << width)]
    (directory / "snapshot.json").write_text(json.dumps(memory), encoding="utf-8")


def lchs_artifacts(directory, original, choices, width):
    inner = Operation.from_program(original)
    caller = Builder("lchs_wide", {"target": Bits(1), "signal": Bits(9), "additional": Bits(width - 1)},
                     attributes={"evolution_alpha": dict(inner.module.attributes)["evolution_alpha"]})

    def fanout():
        with caller.control(caller["target"]):
            for i in range(width - 1):
                caller.x(caller["additional"][i])

    fanout()
    caller.call(inner, target=caller["target"], signal=caller["signal"])
    with caller.adjoint():
        fanout()
    original = save(directory, "open", caller.finish().program())
    for variant, bindings in choices.items():
        save(directory, variant, bind(original, bindings))


def run(*args, reject=None):
    start = perf_counter()
    result = subprocess.run([CLI, *map(str, args)], capture_output=True, text=True, timeout=180)
    elapsed = perf_counter() - start
    if reject is not None:
        assert result.returncode != 0 and reject in result.stderr, (args, result.stdout, result.stderr)
        return None
    assert result.returncode == 0, (args, result.stderr)
    return {**json.loads(result.stdout), "elapsed_seconds": elapsed}


def check_grover(directory):
    reports = []
    for width, iterations in ((1, 1), (3, 2), (5, 4), (8, 12), (12, 50), (16, 4), (128, 2)):
        path = directory / str(width)
        path.mkdir(parents=True, exist_ok=True)
        with_qram = width <= 16
        grover_artifacts(path, width, iterations, with_qram)
        for variant in (("gate", "qram") if with_qram else ("gate",)):
            bound = path / f"{variant}.json"
            args = ("check-grover-wide", variant, width, iterations, path / "open.json",
                    bound, path / "snapshot.json")
            report = run(*args)
            assert report["verified"] and report["address_wires"] == width, report
            assert report["marked_address"] == (1 << (width - 1)), report
            assert report["qram_reads"] == (2 * iterations if variant == "qram" else 0), report
            assert report["peak_private_wires"] == (1 if variant == "qram" else 0), report
            reports.append(report)
            if width <= 5:
                images = json.loads((path / "snapshot.json").read_text()) if variant == "qram" else {}
                result = simulate(loads(bound.read_text(encoding="utf-8")), memory=images)
                observed = sum(abs(amplitude) ** 2 for state, amplitude in result.amplitudes.items()
                               if state[0] == report["marked_address"])
                expected = sin((2 * iterations + 1) * asin(1 / sqrt(1 << width))) ** 2
                assert isclose(observed, expected, abs_tol=1e-10), (observed, expected, report)
    path = directory / "5"
    wrong_image = path / "wrong-image.json"
    wrong_image.write_text(json.dumps({"marks": [int(i == 1) for i in range(32)]}), encoding="utf-8")
    run("check-grover-wide", "qram", 5, 4, path / "open.json", path / "qram.json", wrong_image,
        reject="singleton")
    wrong_program = json.loads((path / "qram.json").read_text())
    provider = next(module for module in wrong_program["modules"] if module["name"] == "wide_mark_qram")
    provider["body"].pop()
    dirty = path / "dirty.json"
    dirty.write_text(json.dumps(wrong_program), encoding="utf-8")
    run("check-grover-wide", "qram", 5, 4, path / "open.json", dirty, path / "snapshot.json",
        reject="bound caller or provider")
    return reports


def check_lchs(directory):
    base = directory / "base"
    base.mkdir(parents=True, exist_ok=True)
    original, choices = lchs(base)
    reports = []
    for width in (2, 4, 8, 16):
        path = directory / str(width)
        path.mkdir(exist_ok=True)
        lchs_artifacts(path, original, choices, width)
        report = run("check-lchs-wide", width, path / "open.json",
                     *(path / f"{variant}.json" for variant in choices))
        assert report["verified"] and report["data_wires"] == width
        assert report["selector_certificates"] == 1 and len(set(report["shared_slots"])) == 4
        assert len(report["bindings"]) == len(choices)
        assert all(result["wires"] == width + 9 and result["quadrature_error"] == "1/50"
                   for result in report["bindings"]), report
        reports.append(report)
    path = directory / "4"
    changed = []
    for name in ("open", "product"):
        artifact = json.loads((path / f"{name}.json").read_text())
        caller = next(module for module in artifact["modules"] if module["name"] == artifact["entry"])
        caller["body"].pop()
        output = path / f"{name}-without-uncompute.json"
        output.write_text(json.dumps(artifact), encoding="utf-8")
        changed.append(output)
    run("check-lchs-wide", 4, *changed, reject="prescribed fanout")
    artifact = json.loads((path / "product.json").read_text())
    caller = next(module for module in artifact["modules"] if module["name"] == artifact["entry"])
    caller["attributes"] = [[key, 0.25 if key == "evolution_alpha" else value]
                            for key, value in caller["attributes"]]
    wrong_scale = path / "wrong-scale.json"
    wrong_scale.write_text(json.dumps(artifact), encoding="utf-8")
    run("check-lchs-wide", 4, path / "open.json", wrong_scale, reject="normalization")
    return reports


def check(directory, workload):
    return {case: test(directory / case) for case, test in
            (("grover", check_grover), ("lchs", check_lchs)) if workload in ("both", case)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, help="keep the checked programs in this directory")
    parser.add_argument("--case", choices=("both", "grover", "lchs"), default="both")
    options = parser.parse_args()
    if options.artifacts is not None:
        options.artifacts.mkdir(parents=True, exist_ok=True)
        print(json.dumps(check(options.artifacts, options.case), indent=2))
    else:
        with tempfile.TemporaryDirectory() as root:
            print(json.dumps(check(Path(root), options.case), indent=2))
