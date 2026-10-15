#!/usr/bin/env python3
"""Regression tests for whole-source Lean admission/axiom guard."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "successor_proof_integrity", HERE / "scripts/check-successor-proof-integrity.py")
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class LexicalProofSafety(unittest.TestCase):
    def test_nested_block_comment_does_not_count(self):
        example = """/-! Intro /- axiom false : False -/ and sorry. -/
theorem foo : True := by trivial
"""
        self.assertEqual(AUDIT.findings(example), [])

    def test_strings_and_line_comments_do_not_count(self):
        example = 'def text := "a string with sorry and \\"admit\\""\n-- axiom surprise : False\n#check True'
        self.assertEqual(AUDIT.findings(example), [])

    def test_admitted_declarations_are_rejected(self):
        example = "theorem bad : True := by sorry\ntheorem bad2 : True := by admit\n"
        self.assertEqual(AUDIT.findings(example), [(1, "sorry"), (2, "admit")])

    def test_axioms_and_constants_are_rejected(self):
        example = "protected axiom impossible : False\nnoncomputable constant unjustified : Nat\n"
        self.assertEqual(AUDIT.findings(example), [
            (1, "protected axiom"), (2, "noncomputable constant")])

    def test_print_axioms_is_not_axiom_declaration(self):
        self.assertEqual(AUDIT.findings("#print axioms My.Theorem\n"), [])

    def test_unterminated_block_comment_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            AUDIT.findings("/- outer /- inner -/ still outer")

    def test_unterminated_string_fails_closed(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            AUDIT.findings('def x := "open')


if __name__ == "__main__":
    unittest.main()
