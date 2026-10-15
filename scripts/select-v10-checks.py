#!/usr/bin/env python3
"""Select every V10 axiom checker affected by changed Lean imports.

On a pull request, compare GitHub's synthetic merge commit with its first
(parent/base) commit. On a push, compare the exact previous main SHA with HEAD.
Follow *transitive* in-repository Lean imports, so changing a dependency
rechecks all consumers. Schedule and manual dispatch run the full audit.
A changed V10 Lean module that no checker imports is a coverage error,
rather than a silently skipped proof. Fail closed if diff discovery fails.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
from pathlib import Path
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PATTERN = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)
CHECKS = sorted((ROOT / "scripts").glob("CheckV10*.lean"))
V10_PREFIX = "SuccessorTree/V10/"
ALWAYS_RECHECK = {
    "lean-toolchain", "lake-manifest.json", "lakefile.toml",
    "scripts/check-axiom-log.py", "scripts/select-v10-checks.py",
    "scripts/run-v10-checks.py",
    "scripts/run-v10-batches.py", "scripts/test_v10_batches.py",
    ".github/workflows/v10-counting.yml", "SuccessorTree.lean",
    "SuccessorTree/V10/All.lean",
}

@lru_cache(maxsize=None)
def closure(relative: str) -> frozenset[str]:
    filename = ROOT / relative
    if not filename.is_file():
        return frozenset({relative})
    deps = {relative}
    for line in PATTERN.findall(filename.read_text(encoding="utf-8")):
        for module in line.split():
            if not module.startswith("SuccessorTree"):
                continue
            dep = module.replace(".", "/") + ".lean"
            if (ROOT / dep).is_file() and dep != relative:
                deps.add(dep)
                deps.update(closure(dep))
    return frozenset(deps)

def changed_paths() -> tuple[set[str], bool]:
    event = os.environ.get("GITHUB_EVENT_NAME")
    if event not in {"push", "pull_request"}:
        return set(), True
    base = "HEAD^1" if event == "pull_request" else os.environ.get(
        "GITHUB_EVENT_BEFORE", "")
    if not base or base == "0" * 40:
        print("Missing previous commit; running ALL V10 audits", file=sys.stderr)
        return set(), True
    try:
        if event == "push":
            # A multi-commit push must include the WHOLE event range, not
            # merely HEAD^; shallow checkouts may omit the before commit.
            present = subprocess.run(
                ["git", "cat-file", "-e", base + "^{commit}"], cwd=ROOT,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                check=False).returncode == 0
            if not present:
                subprocess.check_call(
                    ["git", "fetch", "--no-tags", "--depth=1", "origin", base],
                    cwd=ROOT, stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL)
        data = subprocess.check_output(
            ["git", "diff", "--name-only", "--diff-filter=ACMRD", base, "HEAD"],
            cwd=ROOT, stderr=subprocess.DEVNULL, text=True)
        changed = {x for x in data.splitlines() if x}
        # Source/checker deletions must never disappear from an incremental
        # check selection merely because their imports no longer exist.
        if any(path.endswith(".lean") and not (ROOT / path).is_file()
               for path in changed):
            print("Deleted Lean modules; running ALL V10 audits",
                  file=sys.stderr)
            return changed, True
        return changed, False
    except (subprocess.CalledProcessError, OSError):
        # A missing base or an inaccessible event range must fail CLOSED.
        print("Cannot determine changed files; running ALL V10 audits",
              file=sys.stderr)
        return set(), True

def select(changed: set[str], full: bool) -> list[Path]:
    if full or changed & ALWAYS_RECHECK:
        return CHECKS
    modified = {name for name in changed if name.endswith(".lean")}
    selected = [check for check in CHECKS if closure(check.relative_to(ROOT).as_posix()) & modified]
    affected_sources = {name for name in modified if name.startswith(V10_PREFIX)}
    covered = set().union(*(closure(check.relative_to(ROOT).as_posix()) for check in CHECKS))
    unknown = affected_sources - covered
    if unknown:
        raise RuntimeError("Unaudited changed V10 Lean files:\n" + "\n".join(sorted(unknown)))
    return selected

def regression_scope(changed: set[str], full: bool) -> dict[str, bool]:
    flags = dict(h=False, sigma=False, m3=False, meet=False, pool=False, removal=False)
    if full or changed & ALWAYS_RECHECK:
        return dict.fromkeys(flags, True)
    # Changes to an abstract tree/monoid dependency may affect every V10 model.
    if any(path.startswith("SuccessorTree/") and
           not path.startswith(V10_PREFIX) and path.endswith(".lean")
           for path in changed):
        return dict.fromkeys(flags, True)
    # Foundational V10 changes can affect all finite models.
    foundational = (
        "SuccessorTree/V10/PartialStructure", "SuccessorTree/V10/LocalAge",
        "SuccessorTree/V10/AdmissibleKpt", "SuccessorTree/V10/Canonical",
        "SuccessorTree/V10/RawPrefix", "SuccessorTree/V10/Extract",
        "SuccessorTree/V10/Parameter", "SuccessorTree/V10/Relational",
    )
    if any(path.startswith(foundational) for path in changed):
        return dict.fromkeys(flags, True)
    for path in changed:
        if path.startswith(("SuccessorTree/V10/H", "scripts/check_v10_h")):
            flags["h"] = True
        if path.startswith(("SuccessorTree/V10/Terminal", "scripts/check_v10_terminal")):
            flags["sigma"] = True
        if path.startswith(("SuccessorTree/V10/M3", "scripts/check_v10_m3")):
            flags["m3"] = True
        if path.startswith(("SuccessorTree/V10/KptMeet", "scripts/check_v10_actual_meet")):
            flags["meet"] = True
        if path.startswith(("SuccessorTree/V10/LevelRemoval", "scripts/check_v10_level_removal")):
            flags["removal"] = True
        if path.startswith(("SuccessorTree/V10/OriginalPool", "SuccessorTree/V10/ConcreteOriginalPool",
                            "scripts/check_v10_original_pool")):
            flags["pool"] = True
    return flags

def main() -> None:
    p = argparse.ArgumentParser()
    p.add_argument("--checks-file", type=Path, default=ROOT / "v10-selected-checks.txt")
    p.add_argument("--output-file", type=Path)
    args = p.parse_args()
    changed, full = changed_paths()
    selected = select(changed, full)
    args.checks_file.write_text(
        "".join(str(path.relative_to(ROOT)) + "\n" for path in selected),
        encoding="utf-8")
    scope = regression_scope(changed, full)
    if args.output_file:
        with args.output_file.open("a", encoding="utf-8") as out:
            for key, enabled in scope.items():
                out.write(f"{key}={'true' if enabled else 'false'}\n")
    print(f"V10 audit scope: {len(selected)}/{len(CHECKS)} check scripts;"
          f" {len(changed)} changed files; full={full}; regressions={scope}")
    for check in selected:
        print(f"  {check.relative_to(ROOT)}")

if __name__ == "__main__":
    main()
