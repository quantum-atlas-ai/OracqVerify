"""Export one-bit Deutsch–Jozsa with constant and balanced gate implementations."""

import argparse
import json
from pathlib import Path

from oracq import Bits, Builder, bind, dumps, estimate_resources, loads, unresolved
from oracq.algorithms.basics.oracle_algorithms import deutsch_jozsa
from oracq.algorithms.input_model.oracles import abstract_database


def artifacts() -> dict[str, str]:
    slot = abstract_database("dj_function", address_width=1, data_width=1)
    open_json = dumps(deutsch_jozsa(slot).program(), format="json")
    original = loads(open_json)
    if [item.name for item in unresolved(original)] != ["dj_function"]:
        raise RuntimeError("Expected the one-bit function slot to be open")

    constant = Builder("constant_zero", {"address": Bits(1), "data": Bits(1)})
    balanced = Builder("copy_address", {"address": Bits(1), "data": Bits(1)})
    balanced.xor(balanced["address"], balanced["data"])

    files = {"deutsch_jozsa.open.json": open_json}
    for name, implementation in (("constant", constant), ("balanced", balanced)):
        bound = bind(original, {"dj_function": implementation.finish()})
        if unresolved(bound):
            raise RuntimeError(f"The {name} implementation left unresolved slots")
        bound_json = dumps(bound, format="json")
        ledger = estimate_resources(loads(bound_json)).to_dict()
        files[f"deutsch_jozsa.{name}.json"] = bound_json
        files[f"deutsch_jozsa.{name}.resources.json"] = json.dumps(ledger, indent=2, sort_keys=True) + "\n"
    return files


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify the committed fixtures")
    args = parser.parse_args()
    fixtures = Path(__file__).resolve().parents[1] / "fixtures"
    for name, content in artifacts().items():
        path = fixtures / name
        if args.check:
            if path.read_text(encoding="utf-8") != content:
                parser.exit(status=1, message=f"Stale fixture: {name}\n")
        else:
            path.write_text(content, encoding="utf-8")


if __name__ == "__main__":
    main()
