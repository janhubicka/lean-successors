#!/usr/bin/env python3
"""Adversarial test for import-only umbrella refactors.

Compare the entire transitive source-module closure of SuccessorTree and
SuccessorTree.V10.All with the merge-base versions, using the SAME current
dependencies for both sides. A shorter direct-import list must not silently
drop an intermediate checked module.

When other proof-source files change in the same PR, this check cannot
distinguish intended API changes from lost imports. In that case it explicitly
skips the comparison; normal Lean build and transitive-axiom CI still apply.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
UMBRELLAS = ("SuccessorTree.lean", "SuccessorTree/V10/All.lean")
PATTERN = re.compile(r"^\s*import\s+(.+?)\s*$", re.MULTILINE)


def imports(text: str) -> list[str]:
    return [name for line in PATTERN.findall(text)
            for name in line.split() if name.startswith("SuccessorTree")]


def modules() -> dict[str, str]:
    files = [ROOT / "SuccessorTree.lean"]
    files.extend((ROOT / "SuccessorTree").rglob("*.lean"))
    result = {}
    for file in files:
        name = ".".join(file.relative_to(ROOT).with_suffix("").parts)
        result[name] = file.read_text(encoding="utf-8")
    return result


def closure(start: str, graph: dict[str, list[str]]) -> set[str]:
    seen, queue = set(), [start]
    while queue:
        module = queue.pop()
        if module in seen:
            continue
        if module not in graph:
            raise ValueError(f"missing imported local source module: {module}")
        seen.add(module)
        queue.extend(x for x in graph[module] if x not in seen)
    return seen


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT,
                                   text=True, stderr=subprocess.PIPE)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-ref", default="HEAD^1")
    args = parser.parse_args()
    try:
        changed = set(git("diff", "--name-only", args.base_ref, "HEAD").splitlines())
        modified = set(UMBRELLAS) & changed
        if not modified:
            print("PASS: umbrella imports unchanged")
            return
        other = sorted(path for path in changed if path.endswith(".lean")
                       and path not in UMBRELLAS)
        if other:
            print("SKIP: changed proof sources may intentionally change API:")
            print("\n".join("  " + path for path in other))
            return
        texts = modules()
        current = {name: imports(text) for name, text in texts.items()}
        baseline = {name: deps[:] for name, deps in current.items()}
        for path in UMBRELLAS:
            old = git("show", f"{args.base_ref}:{path}")
            key = ".".join(Path(path).with_suffix("").parts)
            baseline[key] = imports(old)
        for name in ("SuccessorTree", "SuccessorTree.V10.All"):
            before, after = closure(name, baseline), closure(name, current)
            lost, gained = sorted(before - after), sorted(after - before)
            if lost or gained:
                raise ValueError(
                    f"{name} import-closure changed: lost {lost}, gained {gained}")
            print(f"PASS: {name} still reaches {len(after)} source modules; "
                  f"direct imports {len(baseline[name])} -> {len(current[name])}")
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"FAIL: import-umbrella proof obligation: {error}")


if __name__ == "__main__":
    main()
