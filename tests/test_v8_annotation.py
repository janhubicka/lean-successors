"""Guard the validation patcher's label anchors and annotation-only discipline."""
import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / 'manuscript' / 'annotate_successors_v8.py'
if not SCRIPT.exists():
    SCRIPT = Path(__file__).resolve().parents[1] / 'annotate_successors_v8.py'
spec = importlib.util.spec_from_file_location('v8_annotations', SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class AnnotationTests(unittest.TestCase):
    def setUp(self):
        self.tex = '''\n\\begin{algorithm}[Minimal envelope]
  \\label{envelope}
The original algorithm is unchanged.
\\end{algorithm}
\\begin{prop}
  \\label{prop:envelopes}
The original proposition is unchanged.
\\end{prop}
\\begin{observation}
  \\label{obs:closure}
The original observation is unchanged.
\\end{observation}
\\begin{lemma}
  \\label{lem:invariant}
The original invariant is unchanged.
\\end{lemma}
\\begin{lemma}[Punctured-prefix pullback]
  \\label{lem:punctured-prefix}
The original inverse argument is unchanged.
\\end{lemma}
\\begin{theorem}
  \\label{thm:boring1}
The original theorem is unchanged.
\\end{theorem}
\\begin{theorem}
  \\label{thm:boring2}
The original cube theorem is unchanged.
\\end{theorem}
By mistake the colour domain is $\\chi\\colon\\ebinom{\\Sigma^{{\\leq}N}}{Y}\\to r$.
'''
        self.validation = '''\\newcommand{\\leancommit}{9ea16753ee93a09a86fa380a9cdc9055c3fd36a2}
\\newcommand{\\leanverified}[2]{\\marginpar{checked}}
\\newcommand{\\leanpartial}[2]{\\marginpar{partial}}
'''

    def test_inserts_and_preserves_original_prose(self):
        main, markers, notes = mod.annotate(self.tex, self.validation)
        for claim in ('original algorithm', 'original proposition',
                      'original observation', 'original invariant',
                      'original inverse argument', 'original theorem',
                      'original cube theorem'):
            self.assertIn(claim, main)
        for label in mod.REQUIRED:
            self.assertEqual(main.count(f'% BEGIN {mod.STAMP}: {label}'), 1)
        self.assertIn('\\leanenvelopepartial', main)
        self.assertIn('\\leanenvelopeverified', main)
        self.assertIn(mod.COMMIT, markers)
        self.assertIn(r'\ebinom{\Sigma^{{\leq}N}}{X}', main)
        self.assertNotIn(r'\ebinom{\Sigma^{{\leq}N}}{Y}', main)
        self.assertIn('fixed Y to X', ' '.join(notes))

    def test_idempotence(self):
        main, markers, _ = mod.annotate(self.tex, self.validation)
        next_main, next_markers, _ = mod.annotate(main, markers)
        self.assertEqual(main, next_main)
        self.assertEqual(markers, next_markers)
        self.assertEqual(mod.diff_for(main, next_main, 'main.tex'), '')

    def test_rejects_missing_required_label(self):
        missing = self.tex.replace(r'\label{prop:envelopes}', 'NO LABEL')
        with self.assertRaisesRegex(ValueError, 'prop:envelopes'):
            mod.annotate(missing, self.validation)

    def test_punctured_prefix_label_optional(self):
        missing = self.tex.replace(r'\label{lem:punctured-prefix}', 'NO LABEL')
        main, markers, notes = mod.annotate(missing, self.validation)
        self.assertIn('lem:punctured-prefix: found 0 matches', notes)
        self.assertIn('original inverse argument', main)
        self.assertIn(mod.COMMIT, markers)


if __name__ == '__main__':
    unittest.main()
