"""Generate and check one Grover caller under gate and QRAM phase-oracle bindings."""

import argparse
import json
from math import isclose, pi, sin
from pathlib import Path
import subprocess
import tempfile

from oracq import Binding, Bits, Builder, QRAM, bind, declare, dumps, loads, simulate


ROOT = Path(__file__).resolve().parents[1]
CLI = ROOT / ".lake/build/bin/oracq-verify"
THEOREM = "OracqVerify.Generators.Grover.generate_correct"


def artifacts(directory: Path, iterations: int = 1) -> None:
    slot = declare("grover_mark", {"target": Bits(2)}, paradigm="phase_oracle")
    caller = Builder("grover_two_bits", {"target": Bits(2)})
    target = caller["target"]
    caller.h(target)
    with caller.repeat(iterations):
        caller.call(slot, target=target)
        caller.h(target)
        caller.z(target[0])
        caller.z(target[1])
        with caller.control(target[0]):
            caller.z(target[1])
        caller.h(target)
    open_text = dumps(caller.finish().program(), format="json")
    (directory / "open.json").write_text(open_text, encoding="utf-8")
    original = loads(open_text)

    gate = Builder("mark_with_gate", {"target": Bits(2)}, attributes={"oracle_paradigm": "phase_oracle"})
    with gate.control(gate["target"][0]):
        gate.z(gate["target"][1])
    qram = Builder("mark_with_qram", {"target": Bits(2)}, {"lookup": QRAM(2, 1)},
                   attributes={"oracle_paradigm": "phase_oracle"})
    flag = qram.local("flag", Bits(1))
    qram.qram("lookup", qram["target"], flag)
    qram.z(flag)
    qram.qram("lookup", qram["target"], flag)

    for name, implementation in (("gate", gate.finish()), ("qram", Binding(qram.finish(), {"lookup": "marks"}))):
        bound = bind(original, {"grover_mark": implementation})
        (directory / f"{name}.json").write_text(dumps(bound, format="json"), encoding="utf-8")
    (directory / "snapshot.json").write_text('{"marks":[0,0,0,1]}\n', encoding="utf-8")


def check(directory: Path) -> None:
    expected = {"mode": "grover", "marked_address": 3, "iterations": 1, "success_probability": "1"}
    for variant, reads in (("gate", 0), ("qram", 2)):
        report = subprocess.run([CLI, "check-grover", variant, directory / "open.json",
                                 directory / f"{variant}.json", directory / "snapshot.json"],
                                text=True, capture_output=True, check=True)
        assert json.loads(report.stdout) == {**expected, "implementation": variant, "qram_reads": reads}
    (directory / "wrong-snapshot.json").write_text('{"marks":[0,0,1,0]}\n', encoding="utf-8")
    rejected = subprocess.run([CLI, "check-grover", "qram", directory / "open.json",
                               directory / "qram.json", directory / "wrong-snapshot.json"],
                              text=True, capture_output=True)
    assert rejected.returncode != 0 and "marked address" in rejected.stderr
    def command(*arguments, rejected=False):
        result = subprocess.run([CLI, *arguments], text=True, capture_output=True)
        if rejected:
            assert result.returncode != 0, (arguments, result.stdout)
            return result.stderr
        assert result.returncode == 0, (arguments, result.stderr)
        return result.stdout

    assert THEOREM in command("list")
    assert "0 to 3" in command("generate", THEOREM, "4", rejected=True)
    snapshot = directory / "chosen-address.json"
    for address in range(4):
        parameter = str(address)
        emitted = directory / f"lean-{address}.json"
        emitted.write_text(command("generate", THEOREM, parameter), encoding="utf-8")
        for source in (emitted, directory / "open.json"):
            assert json.loads(command("verify", THEOREM, source, parameter))["verified"]
        assert "marked address" in command("verify", THEOREM, emitted,
                                           str((address + 1) % 4), rejected=True)
        snapshot.write_text(json.dumps({"marks": [int(i == address) for i in range(4)]}),
                            encoding="utf-8")
        for source in (emitted, directory / "open.json"):
            report = json.loads(command("verify-bound", THEOREM, source,
                                        directory / "qram.json", parameter, snapshot))
            assert report["marked_address"] == address and report["success_probability"] == "1"
    report = json.loads(command("verify-bound", THEOREM, directory / "open.json",
                                directory / "gate.json", "3", snapshot))
    assert report["implementation"] == "gate" and report["success_probability"] == "1"
    assert "CZ implementation" in command("verify-bound", THEOREM, directory / "open.json",
                                          directory / "gate.json", "2", snapshot, rejected=True)
    for name, edit in (
        ("wrong-phase", lambda body: body[1].update(op="x")),
        ("dirty-flag", lambda body: body.pop()),
    ):
        program = json.loads((directory / "qram.json").read_text(encoding="utf-8"))
        module = next(item for item in program["modules"] if item["name"] == "mark_with_qram")
        edit(module["body"])
        mutated = directory / (name + ".json")
        mutated.write_text(json.dumps(program), encoding="utf-8")
        command("verify-bound", THEOREM, directory / "open.json", mutated, "3", snapshot,
                rejected=True)
    print("Grover: one certified caller, four QRAM addresses, and an interchangeable CZ binding")

    for iterations in (2, 4, 17):
        example = directory / f"iterations-{iterations}"
        example.mkdir()
        artifacts(example, iterations)
        for variant, reads in (("gate", 0), ("qram", 2 * iterations)):
            bound = example / f"{variant}.json"
            paths = (variant, example / "open.json", bound, example / "snapshot.json")
            report = json.loads(command("check-grover", *paths, str(iterations)))
            assert report["iterations"] == iterations and report["qram_reads"] == reads
            assert report["success_probability"] == f"sin^2((2*{iterations}+1)*pi/6)"
            memory = {"marks": [0, 0, 0, 1]} if variant == "qram" else {}
            result = simulate(loads(bound.read_text(encoding="utf-8")), memory=memory)
            probability = sum(abs(amplitude) ** 2 for state, amplitude in result.amplitudes.items() if state[0] == 3)
            assert isclose(probability, sin((2 * iterations + 1) * pi / 6) ** 2, abs_tol=1e-10)
            assert "Unexpected open Grover caller" in command(
                "check-grover", *paths, str(iterations + 1), rejected=True,
            )
    print("Grover: both providers passed at 2, 4, and 17 iterations")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", metavar="DIR", type=Path)
    parser.add_argument("--iterations", type=int, default=1)
    args = parser.parse_args()
    if args.export is not None:
        if args.iterations <= 0:
            parser.error("--iterations must be positive")
        args.export.mkdir(parents=True, exist_ok=True)
        artifacts(args.export, args.iterations)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            artifacts(directory)
            check(directory)
