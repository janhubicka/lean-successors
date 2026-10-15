#!/usr/bin/env python3
"""Fail-closed regression tests for exact V10 batching (no Lean needed)."""
from __future__ import annotations

from collections import Counter
import importlib.util
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("v10_batches", ROOT / "scripts/run-v10-batches.py")
assert spec and spec.loader
batch = importlib.util.module_from_spec(spec)
sys.modules["v10_batches"] = batch
spec.loader.exec_module(batch)


class BatchValidation(unittest.TestCase):
    def test_entire_actual_checker_set_covered_exactly_once(self):
        checks = sorted(p.relative_to(ROOT).as_posix()
                        for p in (ROOT / "scripts").glob("CheckV10*.lean"))
        self.assertGreater(len(checks), 200)
        jobs = batch.partition(checks, 8, 64, ROOT / "scripts/.v10_batches")
        self.assertEqual(Counter(x for job in jobs for x in job.scripts),
                         Counter(checks))
        self.assertTrue(any(j.batched and len(j.scripts) > 1 for j in jobs))
        all_original = Counter(n for p in checks
                               for n in batch.NAMED.findall((ROOT / p).read_text()))
        all_generated = Counter(n for job in jobs for n in
                                batch.NAMED.findall((ROOT / job.lean_file).read_text()))
        self.assertEqual(all_generated, all_original)
        for job in jobs:
            if job.batched:
                actual = batch.NAMED.findall((ROOT / job.lean_file).read_text())
                self.assertEqual(len(actual), len(set(actual)))
                self.assertLessEqual(len(job.scripts), 8)
                self.assertLessEqual(len(actual), 64)

    def test_special_commands_run_verbatim(self):
        with TemporaryDirectory() as dirname:
            root = Path(dirname)
            (root / "scripts").mkdir()
            pure = root / "scripts" / "CheckV10One.lean"
            rich = root / "scripts" / "CheckV10Two.lean"
            pure.write_text("import SuccessorTree.One\n#print axioms A.one\n")
            rich.write_text("import SuccessorTree.Two\nset_option autoImplicit false\n"
                            "#print axioms B.two\n")
            with patch.object(batch, "ROOT", root):
                jobs = batch.partition(
                    ["scripts/CheckV10One.lean", "scripts/CheckV10Two.lean"],
                    8, 64, root / "scripts/.v10_batches")
                self.assertEqual(len(jobs), 2)
                self.assertTrue(jobs[0].batched)
                self.assertFalse(jobs[1].batched)
                self.assertEqual(jobs[1].lean_file, "scripts/CheckV10Two.lean")

    def test_duplicate_endpoints_never_share_batch(self):
        with TemporaryDirectory() as dirname:
            root = Path(dirname)
            (root / "scripts").mkdir()
            for name in ["A", "B"]:
                (root / "scripts" / f"CheckV10{name}.lean").write_text(
                    f"import SuccessorTree.{name}\n#print axioms X.shared\n")
            with patch.object(batch, "ROOT", root):
                jobs = batch.partition(
                    ["scripts/CheckV10A.lean", "scripts/CheckV10B.lean"],
                    8, 64, root / "scripts/.v10_batches")
                self.assertEqual(len(jobs), 2)

    def test_failed_lean_does_not_skip_named_validator(self):
        with TemporaryDirectory() as dirname:
            root = Path(dirname)
            (root / "scripts").mkdir()
            job = batch.Job(("scripts/CheckV10Toy.lean",),
                            "scripts/CheckV10Toy.lean", 1, False)
            with patch.object(batch, "ROOT", root), patch.object(
                    batch.subprocess, "run",
                    return_value=SimpleNamespace(returncode=2)) as call:
                result = batch.check_job(job)
            self.assertFalse(result["passed"])
            self.assertEqual(call.call_count, 1)

    def test_successful_lean_still_checks_exact_named_axioms(self):
        with TemporaryDirectory() as dirname:
            root = Path(dirname)
            (root / "scripts").mkdir()
            job = batch.Job(("scripts/CheckV10Toy.lean",),
                            "scripts/CheckV10Toy.lean", 1, False)
            answers = [SimpleNamespace(returncode=0),
                       SimpleNamespace(returncode=0, stdout="PASS")]
            with patch.object(batch, "ROOT", root), patch.object(
                    batch.subprocess, "run", side_effect=answers) as run:
                result = batch.check_job(job)
            self.assertTrue(result["passed"])
            self.assertEqual(run.call_count, 2)
            self.assertEqual(run.call_args.args[0][-1], job.lean_file)
            self.assertIn("check-axiom-log.py", run.call_args.args[0][1])


if __name__ == "__main__":
    unittest.main()
