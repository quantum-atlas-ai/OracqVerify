"""Check named RIR resolution and actual modular OriginIR-ext exports."""

import json
from pathlib import Path
import subprocess
import tempfile

from oracq import Bits, Builder, QRAM, dumps, fuse
from oracq.infrastructure.backends.originir import export_originir


CLI = Path(__file__).resolve().parents[1] / ".lake/build/bin/oracq-verify"


def run(*args, rejected=False):
    result = subprocess.run([CLI, *args], capture_output=True, text=True)
    if rejected:
        assert result.returncode != 0, (args, result.stdout)
        return result.stderr
    if result.returncode != 0:
        raise AssertionError((args, result.stderr))
    return json.loads(result.stdout)


def save(directory, name, program):
    rir = directory / (name + ".json")
    rir.write_text(dumps(program, format="json"), encoding="utf-8")
    originir = directory / (name + ".originir")
    exported = export_originir(program)
    originir.write_text(exported.text, encoding="utf-8")
    return rir, originir, exported


def check(directory):
    leaf = Builder("rotate", {"bit": Bits(1)})
    leaf.ry(leaf["bit"], 0.25)
    rotation = leaf.finish()
    root = Builder("sliced_rotation", {"control": Bits(1), "target": Bits(2)})
    with root.adjoint():
        with root.control(root["control"]):
            root.call(rotation, bit=root["target"][1])
    gate, target, layout = save(directory, "flat", root.finish().program())
    assert layout.registers == {"control": (0,), "target": (1, 2)}
    assert layout.resources == {} and layout.workspace_qubits == ()
    assert run("check-source", gate)["wires"] == 3
    assert run("check-originir", gate, target)["wires"] == 3
    damaged = directory / "wrong-angle.originir"
    original = target.read_text(encoding="utf-8")
    assert "0.25" in original
    damaged.write_text(original.replace("0.25", "0.5"), encoding="utf-8")
    run("check-originir", gate, damaged, rejected=True)

    leaf = Builder("lookup_and_clear", {"address": Bits(2), "out": Bits(1)}, {"table": QRAM(2, 1)})
    flag = leaf.local("flag", Bits(1))
    leaf.qram("table", leaf["address"], flag)
    with leaf.control(flag):
        leaf.x(leaf["out"])
    leaf.qram("table", leaf["address"], flag)
    inner = leaf.finish()
    root = Builder("sliced_read", {"out": Bits(1), "packed": Bits(2), "tail": Bits(1)}, {"marks": QRAM(2, 1)})
    root.call(inner, address=fuse(root["packed"][1], root["tail"][0]),
              out=root["out"], resources={"table": "marks"})
    qram, target, layout = save(directory, "workspace", root.finish().program())
    assert layout.registers == {"out": (0,), "packed": (1, 2), "tail": (3,)}
    assert layout.resources == {"marks": "ram_marks"} and layout.workspace_qubits == (4,)
    assert run("check-source", qram)["modules"] == 2
    image = directory / "image.json"
    image.write_text('{"marks":[0,1,0,0]}\n', encoding="utf-8")
    report = run("check-originir", qram, target, image)
    assert (report["public_wires"], report["physical_wires"]) == (4, 5)
    lines = target.read_text(encoding="utf-8").splitlines()
    loads = [i for i, line in enumerate(lines) if line.lstrip().startswith("ram_marks ")]
    assert len(loads) == 2
    for name, changed in (
        ("dirty", lines[:loads[1]] + lines[loads[1] + 1:]),
        ("wrong-bank", [line.replace("ram_marks", "ram_other") for line in lines]),
        ("wrong-entry-order", [line.replace("q[2], q[3]", "q[3], q[2]") for line in lines]),
        ("wrong-slice-order", [line.replace("v_packed[1], v_tail[0]", "v_tail[0], v_packed[1]")
                               for line in lines]),
    ):
        assert changed != lines
        damaged = directory / (name + ".originir")
        damaged.write_text("\n".join(changed) + "\n", encoding="utf-8")
        run("check-originir", qram, damaged, image, rejected=True)
    print("RIR and OriginIR-ext: call, slice, adjoint, bank forwarding, and clean workspace")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as directory:
        check(Path(directory))
