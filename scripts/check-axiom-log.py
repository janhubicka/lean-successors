#!/usr/bin/env python3
"""Check a Lean axiom report; accept a fixed count or a file of named checks.

Named checks also reject duplicate, missing or substituted endpoints. A passing
report certifies the listed proof axioms, not equivalence to manuscript prose.
"""
from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re

ALLOWED = frozenset({"propext", "Classical.choice", "Quot.sound"})
ERROR = re.compile(r"\berror(?:\([^\r\n)]*\))?\s*:")
DIRECTIVE = re.compile(r"^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$", re.M)
NAMED_REPORT = re.compile(
    r"'([^'\r\n]+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
    r"|does not depend on any axioms)", re.S)


def declaration_names(source: str) -> list[str]:
    """Read the exact, nonempty list of #print axioms directives."""
    names = DIRECTIVE.findall(source)
    if not names:
        raise ValueError("no named axiom checks in source")
    if len(names) != len(set(names)):
        raise ValueError("duplicate axiom checks in source")
    return names


def check_log(text: str, expected: int | list[str]) -> int:
    if "sorryAx" in text or ERROR.search(text):
        raise ValueError("error or admitted proof in axiom report")
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    reports += [""] * len(re.findall(r"does not depend on any axioms", text))
    count = expected if isinstance(expected, int) else len(expected)
    if count < 1:
        raise ValueError("expected report count must be positive")
    if len(reports) != count:
        raise ValueError(f"expected {count} reports, received {len(reports)}")
    for report in reports:
        actual = {name.strip() for name in report.split(",") if name.strip()}
        if actual - ALLOWED:
            raise ValueError(f"unexpected proof axioms: {sorted(actual - ALLOWED)}")
    if not isinstance(expected, int):
        actual_names = [name for name, _ in NAMED_REPORT.findall(text)]
        wanted, found = Counter(expected), Counter(actual_names)
        if wanted != found:
            raise ValueError(
                f"wrong endpoints: missing {list((wanted - found).elements())}; "
                f"unexpected {list((found - wanted).elements())}")
    return count


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("expected", help="positive report count or Lean check-file path")
    args = parser.parse_args()
    try:
        expected = (int(args.expected) if re.fullmatch(r"[+-]?\d+", args.expected)
                    else declaration_names(Path(args.expected).read_text(encoding="utf-8")))
        count = check_log(args.log.read_text(encoding="utf-8-sig"), expected)
    except (OSError, ValueError) as error:
        raise SystemExit(f"FAIL: {error}") from error
    print(f"PASS: {count} reports use only standard Lean axioms")


if __name__ == "__main__":
    main()
