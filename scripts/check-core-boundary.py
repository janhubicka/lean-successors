#!/usr/bin/env python3
"""Guard the two theorem-library dependency boundaries.

Core contains the full *abstract proofs* but never imports concrete
applications. Library.Structures is an explicitly tiny axioms/data layer
for future M3 experimentation: adding a heavyweight proof import must
require an intentional update of its reviewed dependency manifest.

The import graph is syntactic and this test does NOT certify a proof
or replace Lean elaboration and transitive #print axioms.
"""
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)

CORE_EXCLUDED = (
    "SuccessorTree/V10/",
    "SuccessorTree/FreeAncestral",
)
CORE_ESSENTIAL = {
    "SuccessorTree/HalesJewett/AlphabetInduction.lean",
    "SuccessorTree/ShapeFiniteRamsey.lean",
    "SuccessorTree/ShapeEllentuckRamsey.lean",
    "SuccessorTree/ShapeFiniteCorollaries.lean",
    "SuccessorTree/FatTree/A4ReviewComplete.lean",
    "SuccessorTree/EnvelopeTheorem.lean",
}

# Only these seven source files are allowed in the transitive
# Structure-layer closure. Concrete models and even abstract Ramsey
# theorem proofs must live *above* it, not underneath the M1–M3 types.
STRUCTURES_MANIFEST = {
    "SuccessorTree/Library/Structures.lean",
    "SuccessorTree/Monoid.lean",
    "SuccessorTree/CopyRamsey.lean",
    "SuccessorTree/ShapeEvents.lean",
    "SuccessorTree/ShapePreserving.lean",
    "SuccessorTree/Successor.lean",
    "SuccessorTree/Tree.lean",
}


def closure(start: str, excluded: tuple[str, ...] = ()) -> set[str]:
    pending, seen = [start], set()
    while pending:
        relative = pending.pop()
        if relative in seen:
            continue
        if relative.startswith(excluded):
            raise ValueError(f"import-boundary violation at {relative}")
        file = ROOT / relative
        if not file.is_file():
            raise ValueError(f"missing project dependency: {relative}")
        seen.add(relative)
        for line in IMPORT.findall(file.read_text(encoding="utf-8")):
            for name in line.split():
                if name.startswith("SuccessorTree."):
                    pending.append(name.replace(".", "/") + ".lean")
    return seen


def main() -> None:
    try:
        root = ROOT / "SuccessorTree.lean"
        root_imports = {
            name
            for line in IMPORT.findall(root.read_text(encoding="utf-8"))
            for name in line.split()
        }
        if "SuccessorTree.Core" not in root_imports:
            raise ValueError("full research build must import Core")

        core = closure("SuccessorTree/Core.lean", CORE_EXCLUDED)
        missing = CORE_ESSENTIAL - core
        if missing:
            raise ValueError(f"abstract Core lost endpoints: {sorted(missing)}")

        structures = closure("SuccessorTree/Library/Structures.lean")
        unexpected = structures - STRUCTURES_MANIFEST
        absent = STRUCTURES_MANIFEST - structures
        if unexpected or absent:
            raise ValueError(
                "the lightweight structures import boundary changed: "
                f"unexpected {sorted(unexpected)}, missing {sorted(absent)}"
            )
    except (ValueError, OSError) as error:
        raise SystemExit(f"FAIL: {error}") from error

    print(f"PASS: {len(core)} abstract Core source modules, "
          "no concrete application dependencies")
    print(f"PASS: {len(structures)} structures-only source modules, "
          "no Ramsey theorem/proof imports")


if __name__ == "__main__":
    main()
