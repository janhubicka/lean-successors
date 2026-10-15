#!/usr/bin/env python3
"""Batch only declarative V10 axiom scripts, preserving every named check.

Complex Lean scripts still run verbatim. Generated batch scripts contain
exactly the original imports and #print axioms directives and are validated
with the existing named-endpoint/transitive-axiom checker.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"import\s+([A-Za-z_][A-Za-z0-9_.' ]*)\Z")
AXIOM = re.compile(r"#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_.']*)\Z")
NAMED = re.compile(r"(?m)^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")


@dataclass(frozen=True)
class SimpleCheck:
    path: str
    imports: tuple[str, ...]
    axioms: tuple[str, ...]


@dataclass(frozen=True)
class Job:
    scripts: tuple[str, ...]
    lean_file: str
    endpoints: int
    batched: bool


def read_checks(filename: Path) -> list[str]:
    checks = [x.strip() for x in filename.read_text(encoding="utf-8").splitlines()
              if x.strip()]
    if len(checks) != len(set(checks)):
        raise ValueError("duplicate V10 checker")
    for name in checks:
        path = Path(name)
        if (path.parent != Path("scripts") or
                not path.name.startswith("CheckV10") or
                path.suffix != ".lean" or not (ROOT / path).is_file()):
            raise ValueError(f"not a checked-in V10 checker: {name}")
    return checks


def simple_check(name: str) -> SimpleCheck | None:
    imports, axioms = [], []
    for raw in (ROOT / name).read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if not line or line.startswith("--"):
            continue
        if match := IMPORT.fullmatch(line):
            imports.extend(match.group(1).split())
        elif match := AXIOM.fullmatch(line):
            axioms.append(match.group(1))
        else:
            # This includes module documentation, set_option, examples,
            # run_cmd and all other Lean code: preserve the original file.
            return None
    if not imports or not axioms or len(axioms) != len(set(axioms)):
        return None
    return SimpleCheck(name, tuple(imports), tuple(axioms))


def partition(checks: list[str], batch_size: int, max_axioms: int,
              folder: Path) -> list[Job]:
    folder = folder if folder.is_absolute() else ROOT / folder
    pure, individual = [], []
    for name in checks:
        item = simple_check(name)
        if item is None or len(item.axioms) > max_axioms:
            individual.append(name)
        else:
            pure.append(item)
    groups, group, seen = [], [], set()
    for item in pure:
        if group and (len(group) >= batch_size or
                      len(seen) + len(item.axioms) > max_axioms or
                      seen.intersection(item.axioms)):
            groups.append(group)
            group, seen = [], set()
        group.append(item)
        seen.update(item.axioms)
    if group:
        groups.append(group)
    folder.mkdir(parents=True, exist_ok=True)
    jobs = []
    for i, group in enumerate(groups):
        filename = folder / f"CheckV10Batch{i:03}.lean"
        modules = list(dict.fromkeys(m for item in group for m in item.imports))
        names = [n for item in group for n in item.axioms]
        if len(names) != len(set(names)):
            raise ValueError("duplicate endpoint in generated batch")
        generated = ("".join(f"import {name}\n" for name in modules) + "\n" +
                     "".join(f"#print axioms {name}\n" for name in names))
        parsed = [match.group(1) for line in generated.splitlines()
                  if (match := AXIOM.fullmatch(line))]
        if Counter(parsed) != Counter(names):
            raise ValueError("lost a named axiom check in generated batch")
        filename.write_text(generated, encoding="utf-8")
        jobs.append(Job(tuple(item.path for item in group),
                        filename.relative_to(ROOT).as_posix(), len(names), True))
    for name in individual:
        names = NAMED.findall((ROOT / name).read_text(encoding="utf-8"))
        if not names:
            raise ValueError(f"missing named axiom directive: {name}")
        jobs.append(Job((name,), name, len(names), False))
    if Counter(source for job in jobs for source in job.scripts) != Counter(checks):
        raise ValueError("selected checker coverage changed")
    return jobs


def check_job(job: Job) -> dict:
    log = ROOT / (Path(job.lean_file).stem + "-axioms.log")
    start = time.perf_counter()
    with log.open("w", encoding="utf-8") as out:
        lean = subprocess.run(["lake", "env", "lean", job.lean_file],
                              cwd=ROOT, stdout=out, stderr=subprocess.STDOUT,
                              check=False)
    passed = lean.returncode == 0
    validation = ""
    if passed:
        audit = subprocess.run(
            [sys.executable, "scripts/check-axiom-log.py",
             log.name, job.lean_file],
            cwd=ROOT, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False)
        passed = audit.returncode == 0
        validation = audit.stdout.strip()
    return dict(checks=job.scripts, seconds=round(time.perf_counter()-start, 3),
                passed=passed, batched=job.batched, endpoints=job.endpoints,
                file=job.lean_file, log=log.name,
                lean_returncode=lean.returncode, validation=validation)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checks-file", type=Path,
                        default=ROOT / "v10-selected-checks.txt")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--batch-size", type=int, default=8)
    parser.add_argument("--max-axioms", type=int, default=64)
    parser.add_argument("--timings-file", type=Path,
                        default=ROOT / "v10-check-timings.json")
    args = parser.parse_args()
    if not (1 <= args.jobs <= 4 and 1 <= args.batch_size <= 16 and
            1 <= args.max_axioms <= 256):
        parser.error("invalid worker count or batch limits")
    try:
        checks = read_checks(args.checks_file)
        jobs = partition(checks, args.batch_size, args.max_axioms,
                         ROOT / "scripts/v10_batches_generated")
    except (ValueError, OSError) as error:
        parser.error(str(error))
    print(f"V10: {len(checks)} original scripts, {len(jobs)} bounded jobs, "
          f"{sum(job.batched for job in jobs)} batches and {args.jobs} workers",
          flush=True)
    started = time.perf_counter()
    results = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        tasks = {pool.submit(check_job, job): job for job in jobs}
        for task in as_completed(tasks):
            job = tasks[task]
            try:
                result = task.result()
            except Exception as error:
                result = dict(checks=job.scripts, seconds=0, passed=False,
                              batched=job.batched, file=job.lean_file,
                              error=repr(error))
            results.append(result)
            if not result["passed"]:
                print(f"FAIL {job.lean_file}: "
                      f"{result.get('error', result.get('validation', 'Lean failed'))}",
                      flush=True)
                log = result.get("log")
                if log and (ROOT / log).exists():
                    print("\n".join((ROOT / log).read_text(
                        encoding="utf-8", errors="replace").splitlines()[-65:]),
                        flush=True)
    results.sort(key=lambda x: x["file"])
    covered = sum(len(x["checks"]) for x in results if x["passed"])
    elapsed = round(time.perf_counter()-started, 3)
    args.timings_file.write_text(json.dumps(dict(
        workers=args.jobs, batch_size=args.batch_size, elapsed_seconds=elapsed,
        source_checks=len(checks), passed=covered, results=results),
        indent=2) + "\n", encoding="utf-8")
    print(f"V10 audit: {covered}/{len(checks)} original scripts passed "
          f"in {elapsed}s", flush=True)
    if covered != len(checks):
        raise SystemExit("FAIL: missing or failed V10 checker")


if __name__ == "__main__":
    main()
