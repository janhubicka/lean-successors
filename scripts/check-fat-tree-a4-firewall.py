#!/usr/bin/env python3
"""Independent import firewall for the geometric fat-tree A4 proof.

The geometric fixed-stem fusion must not import its own final A4/Ellentuck
assembly, or a stronger external Ellentuck axiom. This complements (and does
not replace) the Lean kernel and transitive named-axiom audits.
"""
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
START = "SuccessorTree.FatTree.A4ReviewSourceFusion"
FORBIDDEN = {
    "SuccessorTree.FatTree.A4Assembly",
    "SuccessorTree.FatTree.A4ReviewComplete",
    "RamseySpace.AbstractEllentuck",
    "RamseySpace.Ellentuck",
    "RamseySpace.TopologicalRamsey",
}
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)
ADMITTED = re.compile(r"\bsorry\b|\badmit\b|\bsorryAx\b")


def main() -> None:
    visited: set[str] = set()
    queue = [START]
    while queue:
        mod = queue.pop()
        if mod in visited:
            continue
        if mod in FORBIDDEN or "Ellentuck" in mod:
            raise SystemExit(f"FAIL: forbidden A4 circular dependency {mod}")
        visited.add(mod)
        if not mod.startswith("SuccessorTree."):
            continue
        path = ROOT / (mod.replace(".", "/") + ".lean")
        if not path.is_file():
            raise SystemExit(f"FAIL: missing local A4 dependency {path}")
        source = path.read_text(encoding="utf-8")
        if ADMITTED.search(source):
            raise SystemExit(f"FAIL: admission token in geometric proof {path}")
        for line in IMPORT.findall(source):
            for child in line.split():
                if child in FORBIDDEN or "Ellentuck" in child:
                    raise SystemExit(f"FAIL: {path} imports forbidden {child}")
                if child.startswith("SuccessorTree."):
                    queue.append(child)
    print(f"PASS: geometric fixed-stem A4 core traverses {len(visited)} "
          "local modules without circular A4/Ellentuck imports or admissions")


if __name__ == "__main__":
    main()
