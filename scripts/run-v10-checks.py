#!/usr/bin/env python3
"""Run the selected V10 axiom checks independently with bounded parallelism.

Every Lean file gets its own process and log; the existing named #print-axioms
validator still checks every endpoint.  The JSON timings are kept as CI evidence
so later optimizations can be compared to an actual baseline.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def read_checks(filename: Path) -> list[str]:
    checks = [line.strip() for line in filename.read_text(encoding="utf-8").splitlines()
              if line.strip()]
    if len(checks) != len(set(checks)):
        raise ValueError("duplicate V10 check script")
    for check in checks:
        path = Path(check)
        if (path.parent != Path("scripts")
                or not path.name.startswith("CheckV10")
                or path.suffix != ".lean"
                or not (ROOT / path).is_file()):
            raise ValueError(f"not a checked-in V10 axiom script: {check}")
    return checks


def run_check(check: str) -> dict:
    log = ROOT / (Path(check).stem + "-axioms.log")
    start = time.perf_counter()
    with log.open("w", encoding="utf-8") as output:
        lean = subprocess.run(["lake", "env", "lean", check], cwd=ROOT,
                              stdout=output, stderr=subprocess.STDOUT,
                              check=False)
    validation = ""
    okay = lean.returncode == 0
    if okay:
        check_axioms = subprocess.run(
            [sys.executable, "scripts/check-axiom-log.py", log.name, check],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False)
        validation = check_axioms.stdout.strip()
        okay = check_axioms.returncode == 0
    return {
        "check": check,
        "seconds": round(time.perf_counter() - start, 3),
        "passed": okay,
        "lean_returncode": lean.returncode,
        "axiom_validator": validation,
        "log": log.name,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks-file", type=Path, default=ROOT / "v10-selected-checks.txt")
    parser.add_argument("--jobs", type=int, default=min(3, os.cpu_count() or 2))
    parser.add_argument("--timings-file", type=Path, default=ROOT / "v10-check-timings.json")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 8:
        parser.error("jobs must be between 1 and 8")
    try:
        checks = read_checks(args.checks_file)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    print(f"V10: {len(checks)} independent axiom checks; {args.jobs} workers",
          flush=True)
    start = time.perf_counter()
    results: list[dict] = []
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {executor.submit(run_check, name): name for name in checks}
        for future in as_completed(futures):
            name = futures[future]
            try:
                result = future.result()
            except Exception as error:
                result = {"check": name, "seconds": 0, "passed": False,
                          "error": repr(error), "log": ""}
            results.append(result)
            if not result["passed"]:
                print(f"FAIL {name}: {result.get('error', result.get('axiom_validator', 'Lean failed'))}",
                      flush=True)
                logfile = result.get("log")
                if logfile and (ROOT / logfile).exists():
                    print("\n".join((ROOT / logfile).read_text(
                        encoding="utf-8", errors="replace").splitlines()[-60:]),
                        flush=True)
    elapsed = round(time.perf_counter() - start, 3)
    results.sort(key=lambda r: r["check"])
    report = {"workers": args.jobs, "elapsed_seconds": elapsed,
              "checks": len(checks),
              "passed": sum(bool(r["passed"]) for r in results),
              "results": results}
    args.timings_file.write_text(json.dumps(report, indent=2) + "\n",
                                 encoding="utf-8")
    slowest = sorted(results, key=lambda r: -r["seconds"])[:10]
    print(f"V10: {report['passed']}/{len(checks)} passed in {elapsed:.1f}s; slowest checks:")
    for result in slowest:
        print(f"  {result['seconds']:6.1f}s {result['check']}")
    if report["passed"] != len(checks):
        raise SystemExit("FAIL: at least one V10 axiom check failed")


if __name__ == "__main__":
    main()
