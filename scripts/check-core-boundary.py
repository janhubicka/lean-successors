#!/usr/bin/env python3
"""Ensure the abstract successor-tree entry point never imports applications.

Fail closed on missing project-local modules, including transitively imported
modules. This is an import-boundary regression, not a replacement for Lean's
kernel or transitive axiom audit.
"""
from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)
EXCLUDED = (
    "SuccessorTree/V10/",
    "SuccessorTree/FreeAncestral",
    "SuccessorTree/NonPrecompact/",
)
ESSENTIAL = {
    "SuccessorTree/HalesJewett/AlphabetInduction.lean",
    "SuccessorTree/ShapeFiniteRamsey.lean",
    "SuccessorTree/ShapeEllentuckRamsey.lean",
    "SuccessorTree/ShapeFiniteCorollaries.lean",
    "SuccessorTree/FatTree/A4ReviewComplete.lean",
    "SuccessorTree/EnvelopeTheorem.lean",
}


def closure() -> set[str]:
    pending = ["SuccessorTree/Core.lean"]
    seen: set[str] = set()
    while pending:
        relative = pending.pop()
        if relative in seen:
            continue
        if relative.startswith(EXCLUDED):
            raise ValueError(f"abstract core imports application: {relative}")
        path = ROOT / relative
        if not path.is_file():
            raise ValueError(f"missing core dependency: {relative}")
        seen.add(relative)
        for line in IMPORT.findall(path.read_text(encoding="utf-8")):
            for name in line.split():
                if name.startswith("SuccessorTree."):
                    pending.append(name.replace(".", "/") + ".lean")
    return seen


def main() -> None:
    try:
        root = ROOT / "SuccessorTree.lean"
        root_imports = set(
            name for line in IMPORT.findall(root.read_text(encoding="utf-8"))
            for name in line.split())
        if "SuccessorTree.Core" not in root_imports:
            raise ValueError("full SuccessorTree build must import Core")
        modules = closure()
        missing = ESSENTIAL - modules
        if missing:
            raise ValueError(f"core lost endpoints: {sorted(missing)}")
    except (ValueError, OSError) as error:
        raise SystemExit(f"FAIL: {error}") from error
    print(f"PASS: reusable core contains {len(modules)} project modules; "
          "no V10, FreeAncestral, or NonPrecompact imports")


if __name__ == "__main__":
    main()
