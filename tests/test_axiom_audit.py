"""Adversarial regression tests for the shared proof-log checker."""
import importlib.util
from pathlib import Path
import unittest

PATH = Path(__file__).resolve().parents[1] / "scripts" / "check-axiom-log.py"
SPEC = importlib.util.spec_from_file_location("axiom_audit", PATH)
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)

STANDARD = "'P.a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
EMPTY = "'P.b' does not depend on any axioms\n"


class AxiomAuditTests(unittest.TestCase):
    def test_numeric_mode_preserved(self):
        self.assertEqual(audit.check_log(STANDARD + EMPTY, 2), 2)

    def test_named_multiline_and_empty(self):
        self.assertEqual(audit.check_log(STANDARD + EMPTY, ["P.a", "P.b"]), 2)

    def test_report_order_not_significant(self):
        self.assertEqual(audit.check_log(EMPTY + STANDARD, ["P.a", "P.b"]), 2)

    def test_stale_count_rejected(self):
        with self.assertRaisesRegex(ValueError, "expected 1 reports"):
            audit.check_log(STANDARD + EMPTY, 1)

    def test_duplicate_cannot_replace_missing_endpoint(self):
        with self.assertRaisesRegex(ValueError, "wrong endpoints"):
            audit.check_log(STANDARD * 2, ["P.a", "P.b"])

    def test_renamed_endpoint_rejected(self):
        with self.assertRaisesRegex(ValueError, "wrong endpoints"):
            audit.check_log(STANDARD.replace("P.a", "P.c"), ["P.a"])

    def test_unnamed_report_rejected_in_named_mode(self):
        with self.assertRaisesRegex(ValueError, "wrong endpoints"):
            audit.check_log("depends on axioms: [propext]", ["P.a"])

    def test_modern_and_legacy_error_messages(self):
        for error in ("error:", "error(lean.unknownIdentifier):"):
            with self.subTest(error=error), self.assertRaisesRegex(ValueError, "error"):
                audit.check_log(STANDARD + error + " Unknown constant", 1)

    def test_sorry_and_new_axiom_rejected(self):
        for extra in ("sorryAx", "NewTheoremAxiom"):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                audit.check_log(STANDARD.replace("propext", extra), 1)

    def test_source_inventory(self):
        self.assertEqual(audit.declaration_names(
            "import P\n\n#print axioms P.a\n#print axioms P.b\n"), ["P.a", "P.b"])

    def test_empty_and_duplicate_source_rejected(self):
        for source in ("import P\n", "#print axioms P.a\n#print axioms P.a\n"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                audit.declaration_names(source)

    def test_nonpositive_count_rejected(self):
        for count in (0, -1):
            with self.subTest(count=count), self.assertRaises(ValueError):
                audit.check_log("", count)


if __name__ == "__main__":
    unittest.main()
