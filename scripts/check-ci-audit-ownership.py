#!/usr/bin/env python3
"""Keep V10 axiom ownership in exactly one Lean CI workflow.

This is a lightweight structural guard: the dedicated V10 audit dynamically
discovers every CheckV10*.lean and runs the named-axiom verifier, while the
general Lean workflow builds all proof modules and checks *other* endpoints.
The separate v10 batch coverage test checks exact named declaration multisets.
"""
from __future__ import annotations

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    general = (ROOT / ".github/workflows/lean.yml").read_text(encoding="utf-8")
    v10 = (ROOT / ".github/workflows/v10-counting.yml").read_text(encoding="utf-8")
    selector = (ROOT / "scripts/select-v10-checks.py").read_text(encoding="utf-8")
    runner = (ROOT / "scripts/run-v10-batches.py").read_text(encoding="utf-8")
    paths = sorted((ROOT / "scripts").glob("CheckV10*.lean"))
    if len(paths) < 200:
        raise SystemExit("FAIL: expected the full named V10 audit script suite")
    duplicate = re.findall(r"scripts/CheckV10[A-Za-z0-9_]+\.lean", general)
    if duplicate:
        raise SystemExit(f"FAIL: general Lean CI duplicates V10 checks: {duplicate}")
    required_workflow = [
        "push:", "pull_request:", "schedule:",
        "'SuccessorTree/**'", "'scripts/CheckV10*.lean'",
        "scripts/select-v10-checks.py --output-file",
        "scripts/run-v10-batches.py --checks-file v10-selected-checks.txt",
        "scripts/test_v10_batches.py",
        "scripts/check-axiom-log.py",
    ]
    missing = [needle for needle in required_workflow if needle not in v10]
    if missing:
        raise SystemExit(f"FAIL: dedicated V10 workflow missing: {missing}")
    if '.glob("CheckV10*.lean")' not in selector:
        raise SystemExit("FAIL: V10 checker discovery is not exhaustive")
    if "check-axiom-log.py" not in runner or "Counter(" not in runner:
        raise SystemExit("FAIL: exact named/transitive axiom validation missing")
    print(f"PASS: {len(paths)} current V10 named-check scripts have one "
          "dynamic CI owner; general Lean build checks the abstract routes")


if __name__ == "__main__":
    main()
