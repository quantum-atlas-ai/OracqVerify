"""Reproduce the open Bell program, its Oracq binding, and the bound resource ledger."""

import argparse
import json
from pathlib import Path

from oracq import Bits, Builder, ValidationError, bind, dumps, estimate_resources, loads, unresolved
from oracq.algorithms.input_model.oracles import declare


def artifacts() -> dict[str, str]:
    slot = declare("entangle", {"pair": Bits(2)})
    entry = Builder("open_bell", {"pair": Bits(2)})
    entry.h(entry["pair"][0])
    entry.call(slot, pair=entry["pair"])
    open_json = dumps(entry.finish().program(), format="json")

    original = loads(open_json)
    if [slot.name for slot in unresolved(original)] != ["entangle"]:
        raise RuntimeError("Expected one unresolved entangle slot")

    wrong = Builder("wrong_width", {"pair": Bits(1)})
    try:
        bind(original, {"entangle": wrong.finish()})
    except ValidationError as error:
        if "width mismatch" not in str(error):
            raise
    else:
        raise RuntimeError("Oracq accepted a binding with the wrong width")

    entangle = Builder("entangle_impl", {"pair": Bits(2)})
    entangle.xor(entangle["pair"][0], entangle["pair"][1])
    closed = bind(original, {"entangle": entangle.finish()})
    if unresolved(closed):
        raise RuntimeError("Expected all slots to be bound")
    closed_json = dumps(closed, format="json")
    resources = estimate_resources(loads(closed_json)).to_dict()
    return {
        "open_bell.open.json": open_json,
        "open_bell.bound.json": closed_json,
        "open_bell.resources.json": json.dumps(resources, indent=2, sort_keys=True) + "\n",
    }


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
