#!/usr/bin/env python3
"""Generate annotation-only TeX patches, without changing the input manuscript.

Normal use:
  python3 make-validation-patches.py --root /path/to/tex --output /tmp/patches

--reference uses only the main.tex excerpts recovered in the conversation.
Its patches are context-anchored, but are NOT an application test against the
uploaded successor-clean(2).tgz. Use normal mode to regenerate and apply-check
patches against the actual checkout. No network access is used.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

PROOF_COMMIT = '1856f22fa1c94a27b3b282945da7d0f962903cc6'
PROOF_RUN = 'https://github.com/janhubicka/lean-successors/actions/runs/37150740752'
SUPPORT_NAME = 'successor-validation.tex'

# The exact anchors below were read in the recoverable Library main.tex.
# The main theorem's statement is in an input file; we annotate its proof here.
RULES = [
    ('canonical-extension', r'\label{prop:canonical}', r'''
\successorleanverified{SuccessorTree/Canonical.lean}{canonicalExtension\_unique}
\ifshowvalidation
\todo[inline]{Řehořek: The canonical extension is constructed from M2 and M1;
uniqueness is proved afterwards using exact successor preservation on
consecutive image levels. Keep this direction of implication explicit:
existence and uniqueness of canonical extensions have not been shown to be
an equivalent replacement for M2.}
\fi
'''),
    ('fixed-prefix-factor', r'\label{prop:shape-split}', r'''
\successorleanpartial{SuccessorTree/Canonical.lean}{exists\_close\_gap\_factor}
\ifshowvalidation
\todo[inline]{Řehořek: The fixed-prefix splitting needed in the direct Ramsey
proof is checked: the outer factor fixes every node below the cut immediately
above the last prefix image. The transported one-step factorisation is checked
in ShapeExactFactor.lean. This marker covers that core, not every case of the
more general splitting statement above. In the dimension induction, retain
this fixing condition rather than merely asserting equality of ranges.}
\fi
'''),
    ('local-replay-scope', r'\label{lem:pigeonhole1}', r'''
\successorleanpartial{SuccessorTree/ShapePigeonhole.lean}{oneDimensionalPigeonhole\_shape\_AM2}
\ifshowvalidation
\todo[inline]{Řehořek: M3 replay, the finite colour argument and the
$\AM^n_2$ witness are checked in canonical-letter coordinates. The comparison
of the displayed local line with those coordinates should be stated
explicitly. A monochromatic replay line alone must not be used as homogeneity
of all one-step extensions: the checked proof obtains that stronger conclusion
only after the one-moving-level Ramsey theorem, M2 factorisation through a
fixed canonical prefix, and transport into the ambient map.}
\fi
'''),
    ('one-moving-level', r'\label{prop:one-moving-Ramsey}', r'''
\successorleanverified{SuccessorTree/ShapeRamseyFusion.lean}{shapeOneDimensionalRamsey}
\ifshowvalidation
\todo[inline]{Řehořek: This conclusion is now checked for every finite
colouring of $\AM^n_1$, not just for selected replay lines. The Lean proof uses
the two direct large-set fusions and canonical transport; it does not depend
on the fat-tree A4 theorem or an embedding-space Ellentuck conclusion.}
\fi
'''),
    ('finite-dimension', r'\begin{proof}[Proof of Theorem~\ref{thm:shaperamseyN}]', r'''
\successorleanverified{SuccessorTree/ShapeFiniteRamsey.lean}{shapePreservingRamsey}
\ifshowvalidation
\todo[inline]{Řehořek: The finite-dimensional statement is checked for all
$n,k\in\omega$ and arbitrary finite palettes, including $k=0$ and $n=0$.
Make explicit the two invariants used here. First, if the last image level
of a prefix is $i$, its approximation depth is $i+1$, and subsequent right
factors fix $T({\leq}i)$. Second, M2 identifies every one-step extension with
a moving factor composed with the same canonical prefix. Front fusion makes
its colour depend only on that prefix; induction on $k$ finishes the proof.
Canonical-prefix invariance and frozen right factors are checked separately.
The formal theorem also works below an arbitrary prescribed subspace.}
\fi
'''),
    ('validation-boundary', r'\label{sec:finite-direct}', r'''
\successorleaninterface{SuccessorTree/Tree.lean}{LevelTree}
\ifshowvalidation
\todo[inline]{Řehořek: Validation scope: the finite-dimensional theorem is
proved from the encoded tree, shape-map and M1--M3 interfaces. Nonemptiness
of levels is derived from M3, not silently added. The order/level interface
and realised finite approximations must still be compared with the literal
set-theoretic definitions when reading the markers. No marker in this patch
certifies the fat-tree Ramsey-space theorem, the pointwise-Borel transfer,
the composition-Ellentuck statement, or the later applications and envelope
bounds. Preserve their existing review notes.}
\fi
'''),
]

# Only real, retrieved source lines adjacent to an insertion are used as patch
# context. The omitted parts are not reconstructed or represented as inspected.
REFERENCE = r'''\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\begin{document}
%

% [Uninspected material omitted from this test fixture.]

\begin{prop}
	\label{prop:canonical}
	Let $\SNtree$ be an $(\S,\M)$-tree, $n\in \omega$, and $f\in \AM$ with domain $T({\leq}n)$.
	Then there exists a unique $f^+\in \M$ such that $f^+\restriction_{T({\leq} n)}=f$ and

% [Uninspected material omitted from this test fixture.]

\begin{prop}
	\label{prop:shape-split}
	Let $\SNtree$ be an $(\S,\M)$-tree, $n\in \omega$ an integer, $f\in \AM_{n+1}^0$ a shape-preserving function, and $m\in \omega$ an integer satisfying one of the following two conditions:
	\begin{enumerate}

% [Uninspected material omitted from this test fixture.]

\begin{lemma}[1-dimensional pigeonhole]
	\label{lem:pigeonhole1}
	For every $n$ and every finite colouring $\chi$ of~$\AM^n_1$, there exists $h\in \mathcal \AM^n_2$ such that $\chi\restriction_{\{h\circ g:g\in \mathcal L_n\}}$ is constant.
\end{lemma}

% [Uninspected material omitted from this test fixture.]

\subsection{A direct finite-dimensional proof}\label{sec:finite-direct}
The finite-dimensional theorem follows from the preceding finite-trace and large-set arguments without the full fat-tree Ellentuck theorem. The distinction between canonical composites and arbitrary geometric reductions is essential.

% [Uninspected material omitted from this test fixture.]

\begin{prop}[One-moving-level Ramsey theorem]\label{prop:one-moving-Ramsey}
For every $n\in\omega$ and every finite colouring $\chi$ of $\AM^n_1$, there is $F\in\M^n$ such that all $Fg$, $g\in\AM^n_1$, have one colour.
\end{prop}

% [Uninspected material omitted from this test fixture.]

\begin{proof}[Proof of Theorem~\ref{thm:shaperamseyN}]
The case $k=0$ is immediate, and $k=1$ is Proposition~\ref{prop:one-moving-Ramsey}. Proceed by induction on $k\geq2$.

'''


def patch_for(path: str, before: str | None, after: str) -> str:
    if before == after:
        return ''
    header = f'diff --git a/{path} b/{path}\n'
    if before is None:
        header += 'new file mode 100644\n'
    lines = difflib.unified_diff(
        (before or '').splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile='/dev/null' if before is None else f'a/{path}',
        tofile=f'b/{path}', n=1,
    )
    result = [header]
    for line in lines:
        result.append(line)
        if not line.endswith('\n'):
            result.append('\n\\ No newline at end of file\n')
    return ''.join(result)


def insert_annotation(text: str, name: str, anchor: str, body: str) -> str:
    begin = f'% successor-validation:{name}\n'
    end = f'% /successor-validation:{name}\n'
    block = begin + body.strip() + '\n' + end
    if begin in text:
        if text.count(begin) != 1 or block not in text:
            raise ValueError(f'Existing annotation differs: {name}; review it manually')
        return text
    # A commented-out label is not a placement target.
    matches = list(re.finditer(r'^[^%\n]*' + re.escape(anchor) + r'[^\n]*\n',
                               text, re.MULTILINE))
    if len(matches) != 1:
        raise ValueError(f'{name}: expected one uncommented anchor {anchor!r}, found {len(matches)}')
    pos = matches[0].end()
    return text[:pos] + block + text[pos:]


def create_series(source: str, main: str, support: str,
                  existing_support: str | None) -> tuple[list[tuple[str, str]], str]:
    if existing_support is not None and existing_support != support:
        raise ValueError(f'{SUPPORT_NAME} already exists with different content; not overwriting it')
    state = source
    load = r'\input{successor-validation.tex}'
    if load not in state:
        if state.count(r'\begin{document}') != 1:
            raise ValueError('Expected exactly one begin{document} in the main file')
        state = state.replace(r'\begin{document}', load + '\n' + r'\begin{document}', 1)
    series = [('0001-validation-overlay.patch',
               patch_for(SUPPORT_NAME, existing_support, support) + patch_for(main, source, state))]
    for number, (name, anchor, body) in enumerate(RULES, start=2):
        new = insert_annotation(state, name, anchor, body)
        series.append((f'{number:04d}-{name}.patch', patch_for(main, state, new)))
        state = new
    return series, state


def validate_series(source: str, main: str, support_before: str | None,
                    series: list[tuple[str, str]], expected: str, support: str) -> None:
    with tempfile.TemporaryDirectory(prefix='successor-tex-patch-check-') as tmp:
        root = Path(tmp)
        target = root / main
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source, encoding='utf-8')
        if support_before is not None:
            (root / SUPPORT_NAME).write_text(support_before, encoding='utf-8')
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        for name, patch in series:
            if not patch:
                continue
            for args in (['--check'], []):
                run = subprocess.run(['git', '-C', str(root), 'apply', *args, '-'],
                                     input=patch, text=True, capture_output=True)
                if run.returncode:
                    raise ValueError(f'{name}: git apply {args} failed:\n{run.stderr}')
        if target.read_text(encoding='utf-8') != expected:
            raise ValueError('Applied patch series does not reproduce the intended annotated text')
        if (root / SUPPORT_NAME).read_text(encoding='utf-8') != support:
            raise ValueError('Applied support file differs from the pinned template')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, help='Existing TeX checkout (never modified)')
    parser.add_argument('--main', default='main.tex', help='Main TeX file relative to --root')
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--reference', action='store_true', help='Use only recovered excerpt contexts')
    args = parser.parse_args()
    if bool(args.root) == args.reference:
        parser.error('Choose exactly one of --root and --reference')
    relative = Path(args.main)
    if relative.is_absolute() or '..' in relative.parts:
        parser.error('--main must stay inside the supplied checkout')
    support = Path(__file__).with_name(SUPPORT_NAME).read_text(encoding='utf-8')
    if args.reference:
        source, previous_support = REFERENCE, None
        mode = 'recovered-excerpt-contexts; NOT checked against the uploaded archive'
    else:
        source = (args.root / relative).read_text(encoding='utf-8')
        support_path = args.root / SUPPORT_NAME
        previous_support = support_path.read_text(encoding='utf-8') if support_path.exists() else None
        mode = 'actual checkout; patches apply-checked against the supplied input bytes'
    series, final = create_series(source, relative.as_posix(), support, previous_support)
    validate_series(source, relative.as_posix(), previous_support, series, final, support)
    # A second invocation must neither duplicate notes nor generate new edits.
    repeated, final2 = create_series(final, relative.as_posix(), support, support)
    if final2 != final or any(patch for _, patch in repeated):
        raise ValueError('Idempotence regression')
    if args.reference:
        # Check that line offsets and unrelated text between anchors are harmless.
        shifted = ('% unrelated author material\n' * 200) + source
        shifted_series, shifted_final = create_series(shifted, relative.as_posix(), support, None)
        validate_series(shifted, relative.as_posix(), None, series, shifted_final, support)
    args.output.mkdir(parents=True, exist_ok=True)
    written = []
    for name, patch in series:
        if patch:
            (args.output / name).write_text(patch, encoding='utf-8')
            written.append(name)
    combined = patch_for(SUPPORT_NAME, previous_support, support) + patch_for(relative.as_posix(), source, final)
    if combined:
        (args.output / 'all-annotations.patch').write_text(combined, encoding='utf-8')
        validate_series(source, relative.as_posix(), previous_support,
                        [('all-annotations.patch', combined)], final, support)
    manifest = {
        'mode': mode, 'proof_commit': PROOF_COMMIT, 'proof_run': PROOF_RUN,
        'input_main_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'patches': written, 'git_apply_check': 'passed for the stated input mode',
        'idempotence': 'passed', 'full_manuscript_latex_build': 'not performed',
    }
    (args.output / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        raise SystemExit(str(exc)) from exc
