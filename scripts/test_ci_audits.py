#!/usr/bin/env python3
"""Fast, dependency-free regression tests for CI selection and axiom running.

These tests exercise fail-closed behavior; they do not replace Lean theorem
compilation or transitive axiom reports.
"""
from __future__ import annotations

import importlib.util
import os
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]


def load(name: str, path: str):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


selector = load("successor_ci_selector", "scripts/select-v10-checks.py")
runner = load("successor_ci_runner", "scripts/run-v10-checks.py")


class SelectorTests(unittest.TestCase):
    def test_push_uses_complete_before_to_head_range(self):
        with patch.dict(os.environ, {
            "GITHUB_EVENT_NAME": "push",
            "GITHUB_EVENT_BEFORE": "deadbeef",
        }), patch.object(selector.subprocess, "run", return_value=SimpleNamespace(
            returncode=0
        )) as exists, patch.object(
            selector.subprocess, "check_output",
            return_value="SuccessorTree/V10/GPlusFiniteCode.lean\n",
        ) as diff:
            changed, full = selector.changed_paths()
        self.assertFalse(full)
        self.assertEqual(changed, {"SuccessorTree/V10/GPlusFiniteCode.lean"})
        self.assertEqual(diff.call_args.args[0][-2:], ["deadbeef", "HEAD"])
        self.assertEqual(exists.call_args.args[0][1:3], ["cat-file", "-e"])

    def test_missing_push_base_fails_closed(self):
        with patch.dict(os.environ, {
            "GITHUB_EVENT_NAME": "push", "GITHUB_EVENT_BEFORE": "0" * 40,
        }):
            changed, full = selector.changed_paths()
        self.assertTrue(full)
        self.assertFalse(changed)

    def test_unavailable_push_base_fails_closed(self):
        with patch.dict(os.environ, {
            "GITHUB_EVENT_NAME": "push", "GITHUB_EVENT_BEFORE": "abcd",
        }), patch.object(selector.subprocess, "run", return_value=SimpleNamespace(
            returncode=1
        )), patch.object(selector.subprocess, "check_call",
                         side_effect=selector.subprocess.CalledProcessError(
                             1, "git fetch")):
            changed, full = selector.changed_paths()
        self.assertTrue(full)
        self.assertFalse(changed)

    def test_pr_uses_synthetic_merge_base(self):
        with patch.dict(os.environ, {"GITHUB_EVENT_NAME": "pull_request"}), \
             patch.object(selector.subprocess, "check_output",
                          return_value="scripts/CheckV10HUniformEnvelopeBound.lean\n") as diff:
            changed, full = selector.changed_paths()
        self.assertFalse(full)
        self.assertEqual(changed, {"scripts/CheckV10HUniformEnvelopeBound.lean"})
        self.assertEqual(diff.call_args.args[0][-2:], ["HEAD^1", "HEAD"])

    def test_deleted_lean_module_forces_exhaustive_audit(self):
        with patch.dict(os.environ, {"GITHUB_EVENT_NAME": "pull_request"}), \
             patch.object(selector.subprocess, "check_output",
                          return_value="SuccessorTree/V10/RemovedOldExperiment.lean\n"):
            changed, full = selector.changed_paths()
        self.assertTrue(full)
        self.assertIn("SuccessorTree/V10/RemovedOldExperiment.lean", changed)

    def test_affected_checker_selected_transitively(self):
        changed = {"SuccessorTree/V10/HUniformEnvelopeBound.lean"}
        checks = selector.select(changed, False)
        self.assertTrue(any("HUniformEnvelopeBound" in c.name for c in checks),
                        "a concrete modified theorem must select its consumers")


class RunnerTests(unittest.TestCase):
    def test_rejects_check_outside_repository_script_directory(self):
        with TemporaryDirectory() as base:
            root = Path(base)
            (root / "scripts").mkdir()
            allowed = root / "scripts" / "CheckV10Toy.lean"
            allowed.write_text("#print axioms Foo.bar\n", encoding="utf-8")
            listfile = root / "checks.txt"
            listfile.write_text("scripts/CheckV10Toy.lean\n", encoding="utf-8")
            with patch.object(runner, "ROOT", root):
                self.assertEqual(runner.read_checks(listfile),
                                 ["scripts/CheckV10Toy.lean"])
                listfile.write_text("scripts/CheckV10Toy.lean\n"
                                    "scripts/CheckV10Toy.lean\n",
                                    encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "duplicate"):
                    runner.read_checks(listfile)
                listfile.write_text("../external/CheckV10Toy.lean\n",
                                    encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "not a checked-in"):
                    runner.read_checks(listfile)

    def test_validator_not_skipped_after_successful_lean(self):
        with TemporaryDirectory() as base:
            root = Path(base)
            (root / "scripts").mkdir()
            class Completed:
                def __init__(self, returncode=0, stdout="PASS: 1 reports"):
                    self.returncode, self.stdout = returncode, stdout
            with patch.object(runner, "ROOT", root), \
                 patch.object(runner.subprocess, "run",
                              side_effect=[Completed(), Completed()]) as called:
                result = runner.run_check("scripts/CheckV10Toy.lean")
            self.assertTrue(result["passed"])
            self.assertEqual(called.call_count, 2)
            self.assertIn("check-axiom-log.py", called.call_args.args[0][1])
            self.assertEqual(called.call_args.args[0][-1],
                             "scripts/CheckV10Toy.lean")

    def test_failed_lean_does_not_report_success(self):
        with TemporaryDirectory() as base:
            root = Path(base)
            (root / "scripts").mkdir()
            with patch.object(runner, "ROOT", root), \
                 patch.object(runner.subprocess, "run",
                              return_value=SimpleNamespace(returncode=1)) as called:
                result = runner.run_check("scripts/CheckV10Toy.lean")
            self.assertFalse(result["passed"])
            self.assertEqual(called.call_count, 1)


if __name__ == "__main__":
    unittest.main()
