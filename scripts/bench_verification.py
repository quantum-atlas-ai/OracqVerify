"""Measure verifier cost against width, snapshot size, and repeated call sites."""

from argparse import ArgumentParser
import json
import os
from pathlib import Path
from resource import RUSAGE_CHILDREN, getrusage
from statistics import median
from subprocess import CalledProcessError, DEVNULL, PIPE, TimeoutExpired, run
from tempfile import TemporaryDirectory
from time import perf_counter

from oracq import Binding, Bits, Builder, QRAM, bind, dumps
from oracq.algorithms.basics.oracle_algorithms import deutsch_jozsa
from oracq.algorithms.input_model.oracles import abstract_database, declare

from check_generated import CLI as DEFAULT_CLI, DJ_THEOREM


def cpu_seconds() -> float:
    usage = getrusage(RUSAGE_CHILDREN)
    return usage.ru_utime + usage.ru_stime


CLI = Path(os.environ.get("ORACQ_BENCH_VERIFIER", DEFAULT_CLI)).resolve()


def measure(arguments: list[str], repetitions: int, timeout: float = 30, *,
            address_space: int | None = None, discard_output: bool = False) -> dict:
    cpu, wall = [], []
    prefix = ["prlimit", f"--as={address_space}", "--"] if address_space is not None else []
    for _ in range(repetitions + 1):
        start_wall, start_cpu = perf_counter(), cpu_seconds()
        run([*prefix, CLI, *arguments], check=True, text=True, stderr=PIPE,
            stdout=DEVNULL if discard_output else PIPE, timeout=timeout)
        cpu.append(1e3 * (cpu_seconds() - start_cpu))
        wall.append(1e3 * (perf_counter() - start_wall))
    return {"cpu_ms": [round(t, 3) for t in cpu[1:]], "wall_ms": [round(t, 3) for t in wall[1:]],
            "cpu_median_ms": round(median(cpu[1:]), 3), "wall_median_ms": round(median(wall[1:]), 3)}


def save(path: Path, name: str, contents: str) -> str:
    file = path / name
    file.write_text(contents, encoding="utf-8")
    return str(file)


def dj_programs(path: Path, width: int, *, table: bool) -> tuple[str, str]:
    source = deutsch_jozsa(abstract_database("dj_function", width, 1)).program()
    ports = {"address": Bits(width), "data": Bits(1)}
    implementation = Builder("implementation", ports, {"table": QRAM(width, 1)} if table else {})
    if table:
        implementation.qram("table", implementation["address"], implementation["data"])
        binding = Binding(implementation.finish(), {"table": "truth"})
    else:
        implementation.xor(implementation["address"][width - 1], implementation["data"])
        binding = Binding(implementation.finish())
    bound = bind(source, {"dj_function": binding})
    return (save(path, "source.json", dumps(source, format="json")),
            save(path, "bound.json", dumps(bound, format="json")))


def wide_dj_benchmarks(path: Path, repetitions: int) -> list[dict]:
    """Validate the symbolic bit-oracle contract on wide submitted callers."""
    results = []
    for width in (128, 512, 1024):
        source, bound = dj_programs(path, width, table=False)
        args = ["verify-bound", DJ_THEOREM, source, bound, str(width)]
        checked = run([CLI, *args], check=True, text=True, capture_output=True)
        report = json.loads(checked.stdout)
        assert report["verified"] and report["readout"] == "nonzero"
        assert report["resources"]["qubits"] == width + 1
        results.append({"address_width": width, "report": report, **measure(args, repetitions)})
    return results


def standard_benchmarks(path: Path, repetitions: int) -> list[dict]:
    results = [{"workload": "CLI startup", **measure(["list"], repetitions)}]
    for width in (1, 8, 32, 65, 128, 512, 1024):
        source, bound = dj_programs(path, width, table=False)
        result = measure(["verify-bound", DJ_THEOREM, source, bound, str(width)], repetitions)
        results.append({"workload": "bit DJ", "address_width": width, **result})

    for width in (4, 8, 12, 16):
        source, bound = dj_programs(path, width, table=True)
        words = 2 ** width
        memory = save(path, "memory.json", json.dumps({"truth": [index & 1 for index in range(words)]}))
        result = measure(["verify-bound", DJ_THEOREM, source, bound, str(width), memory], repetitions)
        results.append({"workload": "table DJ", "address_width": width, "words": words, **result})

    slot = declare("phase", {"data": Bits(1)})
    implementation = Builder("phase_implementation", {"data": Bits(1)})
    implementation.global_phase(0.625)
    oracle = implementation.finish()
    for sites in (1, 16, 64, 256):
        for distinct in ((False,) if sites == 1 else (False, True)):
            entry = Builder("main", {"data": Bits(sites if distinct else 1), "guard": Bits(1)})
            with entry.control(entry["guard"], 1):
                for index in range(sites):
                    entry.call(slot, data=entry["data"][index if distinct else 0])
            source = entry.finish().program()
            bound = bind(source, {"phase": oracle})
            files = [save(path, "source.json", dumps(source, format="json")),
                     save(path, "bound.json", dumps(bound, format="json"))]
            result = measure(["check-link", *files], repetitions)
            results.append({"workload": "controlled phase", "calls": sites,
                            "distinct_sites": sites if distinct else 1, **result})

    return results


def paper_benchmarks(path: Path, repetitions: int) -> list[dict]:
    from check_wide_cases import grover_artifacts

    results = standard_benchmarks(path, repetitions)
    for width, iterations, variants in ((16, 4, ("gate", "qram")), (128, 2, ("gate",))):
        grover_artifacts(path, width, iterations, with_qram="qram" in variants)
        for variant in variants:
            args = ["check-grover-wide", variant, str(width), str(iterations),
                    str(path / "open.json"), str(path / f"{variant}.json"), str(path / "snapshot.json")]
            results.append({"workload": "wide Grover", "address_width": width, "iterations": iterations,
                            "provider": variant, **measure(args, repetitions)})
    return results


def scoped_benchmarks(path: Path, repetitions: int, timeout: float = 60) -> list[dict]:
    """Compare both binding checkers on the same shared, workspace-free call graph."""
    ports = {"data": Bits(1)}
    slot = declare("shared", ports)
    caller = Builder("shared_caller", {"data": Bits(1), "guard": Bits(1)})
    with caller.control(caller["guard"]):
        caller.call(slot, data=caller["data"])
    source_program = caller.finish().program()
    source = path / "source.json"
    source.write_text(dumps(source_program, format="json"), encoding="utf-8")
    base = Builder("shared_0", ports)
    for _ in range(16):
        base.ry(base["data"], 0.125)
    implementation = base.finish()
    results = []
    depths = (0, 4, 8, 10, 14, 18, 20)
    memory = 4 * 1024**3
    for depth in range(max(depths) + 1):
        if depth > 0:
            parent = Builder(f"shared_{depth}", ports)
            for _ in range(2):
                parent.call(implementation, data=parent["data"])
            implementation = parent.finish()
        if depth not in depths:
            continue
        bound = path / "bound.json"
        program = bind(source_program, {"shared": implementation})
        bound.write_text(dumps(program, format="json"), encoding="utf-8")
        flat = ["check-link", str(source), str(bound)]
        scoped = ["check-scoped-link", str(source), str(bound)]
        scoped_check = run([CLI, *scoped], check=True, text=True, capture_output=True, timeout=timeout)
        scoped_result = json.loads(scoped_check.stdout)
        expanded = 16 * 2 ** depth
        assert len(scoped_result["bound"]) == depth + 3
        try:
            if depth <= 10:
                flat_check = run([CLI, *flat], check=True, text=True, capture_output=True, timeout=timeout)
                assert json.loads(flat_check.stdout)["closed_instructions"] == expanded
            flat_timing = measure(flat, repetitions, timeout, address_space=memory, discard_output=True)
        except TimeoutExpired:
            flat_timing = {"timeout_seconds": timeout}
        except CalledProcessError as error:
            flat_timing = {"returncode": error.returncode, "diagnostic": error.stderr.strip()}
        results.append({"depth": depth, "expanded_instructions": expanded,
                        "scoped_definitions": len(scoped_result["bound"]),
                        "flat": flat_timing, "scoped": measure(scoped, repetitions, timeout,
                                                               address_space=memory, discard_output=True)})
    return results


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--repetitions", type=int, default=9)
    workloads = parser.add_mutually_exclusive_group()
    workloads.add_argument("--paper", dest="benchmark", action="store_const", const=paper_benchmarks,
                           help="measure the public width and call-site workloads")
    workloads.add_argument("--scoped", dest="benchmark", action="store_const", const=scoped_benchmarks,
                           help="compare flat and scoped validation")
    workloads.add_argument("--wide-dj", dest="benchmark", action="store_const", const=wide_dj_benchmarks,
                           help="measure symbolic bit-oracle validation at larger widths")
    parser.set_defaults(benchmark=paper_benchmarks)
    options = parser.parse_args()
    if options.repetitions < 1:
        parser.error("--repetitions must be positive")
    with TemporaryDirectory() as directory:
        print(json.dumps(options.benchmark(Path(directory), options.repetitions), indent=2))
