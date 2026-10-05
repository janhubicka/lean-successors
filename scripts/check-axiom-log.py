#!/usr/bin/env python3
"""Check a Lean axiom report without treating conditional theorems as unconditional."""
from __future__ import annotations

import argparse
from pathlib import Path
import re


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("expected", type=int)
    args = parser.parse_args()
    if args.expected < 1:
        parser.error("expected report count must be positive")
    text = args.log.read_text(encoding="utf-8")
    if "sorryAx" in text or re.search(r"\berror:", text):
        raise SystemExit("FAIL: error or admitted proof in axiom report")
    reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    reports += [""] * len(re.findall(r"does not depend on any axioms", text))
    if len(reports) != args.expected:
        raise SystemExit(f"FAIL: expected {args.expected} reports, received {len(reports)}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for report in reports:
        actual = {name.strip() for name in report.split(",") if name.strip()}
        if actual - allowed:
            raise SystemExit(f"FAIL: unexpected proof axioms: {sorted(actual - allowed)}")
    print(f"PASS: {len(reports)} reports use only standard Lean axioms")


if __name__ == "__main__":
    main()
