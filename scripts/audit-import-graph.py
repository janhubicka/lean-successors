#!/usr/bin/env python3
"""Static import and proof-risk inventory for the successor library.

This is intentionally a REPORT, not an automatic dead-code remover. Lean modules
can be imported directly by downstream libraries even if the umbrella file and
local axiom-check scripts do not import them. Review every orphan before deletion.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)
RISK = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom_declaration": re.compile(r"(?m)^\s*axiom\s+"),
    "unsafe_declaration": re.compile(r"(?m)^\s*unsafe\s+"),
    "native_decide": re.compile(r"\bnative_decide\b"),
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "successor-import-audit.json")
    args = parser.parse_args()

    source_files = sorted((ROOT / "SuccessorTree").rglob("*.lean"))
    source_files.append(ROOT / "SuccessorTree.lean")
    check_files = sorted((ROOT / "scripts").glob("Check*.lean"))
    all_files = source_files + check_files
    by_module: dict[str, Path] = {
        ".".join(file.relative_to(ROOT).with_suffix("").parts): file
        for file in all_files
    }
    imports: dict[str, set[str]] = {}
    risk: dict[str, dict[str, int]] = {}
    for module, file in by_module.items():
        data = file.read_text(encoding="utf-8")
        imports[module] = {
            dep for line in IMPORT.findall(data) for dep in line.split()
            if dep in by_module
        }
        flagged = {name: len(pattern.findall(data))
                   for name, pattern in RISK.items()}
        if any(flagged.values()):
            risk[file.relative_to(ROOT).as_posix()] = {
                name: count for name, count in flagged.items() if count
            }

    def closure(starts: set[str]) -> set[str]:
        seen: set[str] = set()
        queue = list(starts)
        while queue:
            module = queue.pop()
            if module in seen or module not in by_module:
                continue
            seen.add(module)
            queue.extend(imports[module] - seen)
        return seen

    umbrella = closure({"SuccessorTree"})
    check_roots = {name for name in by_module if name.startswith("scripts.Check")}
    checked = closure(check_roots)
    source_modules = set(by_module) - check_roots
    # Modules outside BOTH the public umbrella and local check scripts are
    # candidates for review, not necessarily dead: downstream users may import.
    orphans = sorted(source_modules - umbrella - checked)
    paths = lambda names: [by_module[x].relative_to(ROOT).as_posix()
                            for x in sorted(names)]
    dependents = Counter(d for deps in imports.values() for d in deps)
    report = {
        "source_modules": len(source_modules),
        "check_scripts": len(check_files),
        "umbrella_reachable": len(source_modules & umbrella),
        "locally_checked_reachable": len(source_modules & checked),
        "orphan_candidates": paths(orphans),
        "largest_orphan_candidates": sorted(
            [{"path": by_module[m].relative_to(ROOT).as_posix(),
              "bytes": by_module[m].stat().st_size} for m in orphans],
            key=lambda o: -o["bytes"])[:30],
        "most_direct_imported_modules": [
            {"module": name, "importers": count}
            for name, count in dependents.most_common(30)
        ],
        "source_risk_tokens_including_comments": risk,
        "interpretation": (
            "Import graph is syntactic. Orphans may be public standalone APIs; "
            "risk counts include comments and are NOT proof-hole findings. "
            "No file is deleted and no axiom status is inferred."
        ),
    }
    args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Import inventory: {len(source_modules)} source modules, "
          f"{len(check_files)} check scripts; {len(orphans)} orphan candidates")
    for path in paths(orphans)[:30]:
        print("  candidate: " + path)
    print(f"Risk-token matches (including comments): {len(risk)} files; "
          "inspect individually rather than treating as proof holes")
    print(f"Full report: {args.output}")


if __name__ == "__main__":
    main()
