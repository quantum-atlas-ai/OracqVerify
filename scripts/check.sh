#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

oracq_requirement='oracq @ git+https://github.com/IAI-USTC-Quantum/oracq.git@3dbd194f0cae2217d41112123db2aadb74a44caf'
uv run --no-project --with "$oracq_requirement" python scripts/export_open_bell.py --check
uv run --no-project --with "$oracq_requirement" python scripts/export_deutsch_jozsa.py --check
lake build
uv run --no-project --with "$oracq_requirement" python scripts/check_grover.py
uv run --no-project --with "$oracq_requirement" python scripts/check_wide_cases.py
uv run --no-project --with "$oracq_requirement" python scripts/check_approximate_phase.py --repetitions 1
uv run --no-project --with "$oracq_requirement" python scripts/check_translation.py
uv run --no-project --with "$oracq_requirement" python scripts/check_replacements.py
uv run --no-project --with "$oracq_requirement" python scripts/check_generated.py
uv run --no-project --with "$oracq_requirement" python scripts/check_lchs_semantics.py
