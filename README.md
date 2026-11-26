# OracqVerify

OracqVerify is the Lean 4 implementation accompanying *Verifying Quantum Programs Before Oracle Binding*. It generates certified quantum programs with open oracle slots and independently checks programs supplied by [Oracq](https://github.com/IAI-USTC-Quantum/oracq) or another producer. Its linking theorems transfer a proof about an open caller to a checked binding when the selected implementations satisfy their contracts.

Programs use Oracq's register-level intermediate representation (RIR). A binding can supply a gate circuit or a coherent read from a fixed, read-only QRAM snapshot. The checked call structure includes ordered register views, bank forwarding, and the placement of control and adjoint. Case-specific checkers certify matrix actions, clean workspace, or quantitative error bounds for the supported fragments.

## Build and check

Install [Elan](https://github.com/leanprover/elan) for Lean, and [uv](https://docs.astral.sh/uv/) with Python 3.11 or newer for the reproduction scripts. The toolchain and Lake manifest pin Lean 4.35.0, [Qatlib](https://github.com/quantum-atlas-ai/qatlib), and all transitive Lean dependencies. The Python scripts use a pinned public Oracq revision.

```sh
# Optional. Fetch precompiled public dependencies to save build time.
lake exe @Qatlib/get_cache
lake build
bash scripts/check.sh
```

The check script compares regenerated fixtures, builds the Lean targets, exercises both the Lean generation and Python binding paths, and checks that mutated programs are rejected. The first build can take longer when dependency caches are unavailable.

## Generate and verify a program

```sh
verifier=.lake/build/bin/oracq-verify
"$verifier" list

theorem=OracqVerify.Generators.DeutschJozsa.generate_correct
"$verifier" generate "$theorem" 3 > dj.open.json
"$verifier" verify "$theorem" dj.open.json 3
```

This generator accepts any positive address width. The generated RIR has a single XOR oracle slot. The theorem proves the Deutsch–Jozsa readout rule under the constant-or-balanced promise. The Grover generator takes a marked address from zero to three.

## Verify a late binding

```sh
oracq_requirement='oracq @ git+https://github.com/IAI-USTC-Quantum/oracq.git@3dbd194f0cae2217d41112123db2aadb74a44caf'
uv run --no-project --with "$oracq_requirement" python scripts/check_grover.py --export grover

verifier=.lake/build/bin/oracq-verify
"$verifier" check-grover gate grover/open.json grover/gate.json grover/snapshot.json
"$verifier" check-grover qram grover/open.json grover/qram.json grover/snapshot.json
```

Both checks report success probability `1` for this two-bit, one-iteration search. The gate implementation uses zero QRAM reads and the QRAM implementation uses two, with the second restoring a private flag. Changing the snapshot to mark a different address causes the QRAM check to reject the binding.

## Reproduce the paper

| Case | Reproduction entry point |
| --- | --- |
| Deutsch–Jozsa generation, binding, and readout | `scripts/check_generated.py` |
| Grover gate and QRAM bindings | `scripts/check_grover.py` |
| Wider Grover and LCHS instances | `scripts/check_wide_cases.py` |
| Controlled approximate phase binding | `scripts/check_approximate_phase.py` |
| LCHS, sparse block encoding, and amplitude amplification replacements | `scripts/check_replacements.py` |
| Named RIR and supported OriginIR-ext translations | `scripts/check_translation.py` |

Run the scripts with the pinned Oracq environment from the example above. `bench_verification.py --paper --repetitions 3` and `bench_verification.py --scoped --repetitions 3` run the main timing workloads. The scoped timing mode uses Linux `prlimit`. To reproduce the CPU-affinity protocol, run each timing batch on one pinned logical CPU. The public executable has fewer initialization dependencies than the development executable used for the reported timings.

The LCHS linking result gives an operator-norm bound of `1/50` relative to the specified finite quadrature. CLI reports apply to decoded RIR and supplied snapshots. The paper explains the trusted boundary for byte parsing, native evaluation, and interpreting the CLI report.

Run `lake env lean scripts/audit_axioms.lean` to inspect the dependencies of the linking, generation, and case-study proofs. The two native decisions in the fixed nine-wire standalone LCHS arithmetic check appear at the end of the report.

## License

[MIT](LICENSE). Dependencies are distributed under their own licenses.
