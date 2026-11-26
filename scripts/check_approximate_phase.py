"""Exercise the compiled quantitative scoped linker on serialized phase callers."""

import argparse
from fractions import Fraction
import json
from pathlib import Path
from statistics import median
import subprocess
from tempfile import TemporaryDirectory
from time import perf_counter

from oracq import Bits, Builder, declare, dumps

from check_generated import CLI


def artifacts(directory, rounds, implementation_angle=0.2509765625):
    ports = {"data": Bits(1)}
    slot = declare("phase_slot", ports, paradigm="phase_oracle")
    impl = Builder("phase_slot", ports, attributes={"oracle_paradigm": "phase_oracle"})
    impl.global_phase(implementation_angle)

    def program(provider):
        root = Builder("phase_caller", {"data": Bits(1), "guard": Bits(1)})
        with root.repeat(rounds):
            with root.control(root["guard"]):
                root.call(provider, data=root["data"])
            with root.adjoint():
                root.call(provider, data=root["data"])
        return root.finish().program()

    original, bound = directory / "open.json", directory / "bound.json"
    original.write_text(dumps(program(slot), format="json"), encoding="utf-8")
    bound.write_text(dumps(program(impl.finish()), format="json"), encoding="utf-8")
    return original, bound


def check(directory, repetitions):
    def command(original, bound, rounds, limit):
        return [CLI, "check-approx-phase", original, bound, "0.25", str(rounds), str(limit)]

    results = []
    for rounds in (1, 8, 64, 512):
        path = directory / str(rounds)
        path.mkdir(parents=True, exist_ok=True)
        original, bound = artifacts(path, rounds)
        elapsed = []
        for _ in range(repetitions + 1):
            start = perf_counter()
            process = subprocess.run(command(original, bound, rounds, 1), capture_output=True, text=True, check=True)
            elapsed.append(perf_counter() - start)
            report = json.loads(process.stdout)
            assert report["verified"] and report["slot_calls"] == 2 * rounds
            assert Fraction(report["slot_error"]) == Fraction(1, 1024)
            assert Fraction(report["operator_error"]) == Fraction(rounds, 512)
        results.append({**report, "median_seconds": median(elapsed[1:]), "samples_seconds": elapsed[1:]})
    path = directory / "64"
    rejected = subprocess.run(command(path / "open.json", path / "bound.json", 64, 0.0625),
                              capture_output=True, text=True, check=False)
    assert rejected.returncode != 0 and "exceeds" in rejected.stderr
    rejected = subprocess.run(command(path / "open.json", path / "bound.json", 63, 1),
                              capture_output=True, text=True, check=False)
    assert rejected.returncode != 0 and "call pairs" in rejected.stderr
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path)
    parser.add_argument("--repetitions", type=int, default=3)
    args = parser.parse_args()
    if args.repetitions < 1:
        parser.error("--repetitions must be positive")
    if args.artifacts is not None:
        print(json.dumps(check(args.artifacts, args.repetitions), indent=2))
    else:
        with TemporaryDirectory() as path:
            print(json.dumps(check(Path(path), args.repetitions), indent=2))
