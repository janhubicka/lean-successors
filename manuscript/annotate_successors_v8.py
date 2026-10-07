#!/usr/bin/env python3
"""Add validation markers, Řehořek TODOs, and one mechanical correction to v8.

Usage:
  python3 annotate_successors_v8.py --root /path/to/tex/tree \
      --patch successors-v8-validation-addendum.patch
  python3 annotate_successors_v8.py --root /path/to/tex/tree --apply
  python3 annotate_successors_v8.py --archive successors-v8-reviewed.tgz \
      --patch successors-v8-validation-addendum.patch \
      --output successors-v8-envelope-annotated.tgz

The source changes are anchored to existing LaTeX labels, not line numbers,
and are idempotent. The script refuses to edit when required anchors are missing
or ambiguous, and writes no changes unless --apply/--output is specified.
"""
import argparse
import difflib
from pathlib import Path
import re
import tarfile
import tempfile

COMMIT = '0dc4dc4d7fb7169ea3acd4461ef734df2c5b0169'
STAMP = 'successor-v8-validation-20261008'

VALIDATION_MACROS = r'''
% BEGIN successor-v8-validation-20261008: Section 5 markers
% Section 5 endpoints are checked on PR #107 at the following fixed SHA.
% CI: https://github.com/janhubicka/lean-successors/actions/runs/37657309674
%     https://github.com/janhubicka/lean-successors/actions/runs/37657309826
% The verification is for the typed SMTree interface, not for the separate
% set-theoretic LevelTree adapter or every sentence of the paper proof.
\newcommand{\leanenvelopecommit}{0dc4dc4d7fb7169ea3acd4461ef734df2c5b0169}
\newcommand{\leanenvelopeverified}[2]{%
  \begingroup\renewcommand{\leancommit}{\leanenvelopecommit}%
  \leanverified{#1}{#2}\endgroup}
\newcommand{\leanenvelopepartial}[2]{%
  \begingroup\renewcommand{\leancommit}{\leanenvelopecommit}%
  \leanpartial{#1}{#2}\endgroup}
% END successor-v8-validation-20261008: Section 5 markers
'''.strip('\n')

# The new text matches the manuscript house style.  We do not replace any
# mathematical statement or proof; one X/Y typo is corrected if still present.
ANNOTATIONS = {
 'envelope': r'''
\leanenvelopeverified{SuccessorTree/EnvelopeRunExistence.lean}{algorithmRun\_nonempty}
\todo[inline]{Řehořek: Algorithm~\ref{envelope} has a finite Lean construction for nonempty $X$. Keep the empty-set return $(\mathrm{Id},\emptyset)$ separate: its height is $0$, while the Lean run for a chosen top level is the nonempty branch. The membership test in (I3) is well-defined by the failure of (I2), formalised as \texttt{nextPrefix\_eq\_of\_no\_meet}.}
''',
 'obs:closure': r'''
\leanenvelopeverified{SuccessorTree/Envelope.lean}{envelope\_closure}
\todo[inline]{Řehořek: Observation~\ref{obs:closure} is checked for total maps. In the minimality argument, a competing envelope may lie in $\AM$; use the finite-prefix version as well (\texttt{prefixEnvelope\_closure} in \texttt{EnvelopePrefix.lean}). Do not infer coverage by an arbitrary finite approximation merely from the total-map statement.}
''',
 'lem:punctured-prefix': r'''
\leanenvelopeverified{SuccessorTree/EnvelopePullback.lean}{subset\_range\_of\_oneLevel}
\leanenvelopeverified{SuccessorTree/EnvelopeUniqueness.lean}{preimage\_eq\_of\_oneLevel}
\todo[inline]{Řehořek: For an intermediate prefix $a|_j$, assert $a|_j\in H_i[T]$; the conclusion $a\in H_i[T]$ follows on taking $j=\ell(a)$. The local inverse is determined by the crossing data, using (E1) and successor injectivity. These two claims are checked separately.}
''',
 'lem:invariant': r'''
\leanenvelopeverified{SuccessorTree/EnvelopeRun.lean}{AlgorithmRun.fullInvariant}
\todo[inline]{Řehořek: Strengthen the induction invariant by recording that $F_i$ fixes every source level below $i$. This is needed when applying the punctured-prefix pullback at stage $i$, and is preserved by both branches. The strengthened invariant, including the exact retained/skipped-level set, is proved in \texttt{EnvelopeInvariantLevels.lean}.}
''',
 'prop:envelopes': r'''
\leanenvelopepartial{SuccessorTree/EnvelopeHeight.lean}{minimal\_output\_height\_AM}
\todo[inline]{Řehořek: The nonempty case of this proposition is kernel-checked on PR~\#107: \texttt{AlgorithmRun.I\_eq}, \texttt{AlgorithmRun.embeddingType\_eq}, \texttt{minimal\_output\_height\_AM}, and existence of a run. The orange marker records that the empty case is handled directly in the manuscript and that the displayed proof still needs the corrections below. Do not treat the check as certification of the current prose.}
''',
 'thm:boring1': r'''
\todo[inline]{Řehořek: The claim that Algorithm~\ref{envelope} gives precisely the simultaneous-deletion type $\tau_{\mathcal E}$ is not justified by (B1)--(B2). For an explicit failure of type invariance let $\Sigma=\{0,1\}$, $\mathcal E_0=\{\text{constant }0\}$, $\mathcal E_1=\{\text{first-coordinate projection}\}$, and $\mathcal E_n$ consist of all functions for $n\geq2$. These satisfy (B1)--(B2). The map $P(w)=0w$ belongs to $\mathcal M_{\mathcal E}$, yet for $Y=\{00,10\}$ we have $I_{\mathcal E}(Y)=\{0,1,2\}$ and $\tau_{\mathcal E}(Y)=\{00,10\}$, whereas $I_{\mathcal E}(P[Y])=\{1,3\}$ and $\tau_{\mathcal E}(P[Y])=\{0,1\}$. Repair the type/reconstruction lemma or add a justified extra hypothesis before marking this application verified. This contradicts the proof step, not necessarily the theorem's Ramsey conclusion.}
''',
 'thm:boring2': r'''
\todo[inline]{Řehořek: The same type-invariance dependency affects the cube theorem. Exact-end padding alone does not repair the correspondence. Keep this theorem unvalidated until the reconstruction lemma is established under the stated hypotheses or a revised type is adopted.}
''',
}

# Hard required labels are unchanged in the indexed manuscript and v8 review.
REQUIRED = ('envelope', 'obs:closure', 'lem:invariant', 'prop:envelopes',
            'thm:boring1', 'thm:boring2')


def add_after_label(source, label, insertion):
    sentinel = f'% BEGIN {STAMP}: {label}'
    if sentinel in source:
        return source, 'already'
    pat = re.compile(r'(?m)^([^\n]*\\label\{' + re.escape(label) + r'\}[^\n]*)(\n|$)')
    matches = list(pat.finditer(source))
    if len(matches) != 1:
        return source, f'found {len(matches)} matches'
    m = matches[0]
    note = '\n' + sentinel + '\n' + insertion.strip('\n') + '\n' + f'% END {STAMP}: {label}'
    # Insert after the line bearing the label; existing surrounding prose stays.
    return source[:m.end(1)] + note + source[m.end(1):], 'inserted'


def annotate(main_source, validation_source):
    if '\\leanverified' not in validation_source or '\\leanpartial' not in validation_source:
        raise ValueError('Expected existing \\leanverified and \\leanpartial macros in validation.tex')
    log = []
    new_main = main_source
    for label, content in ANNOTATIONS.items():
        new_main, status = add_after_label(new_main, label, content)
        log.append(f'{label}: {status}')
        if label in REQUIRED and status not in ('already', 'inserted'):
            raise ValueError('Required anchor ' + label + ': ' + status)
    # The colour domain in the proof of thm:boring1 is copies of X, not Y:
    # the very next formula evaluates chi at f[tau_E(X)].  A purely mechanical
    # X/Y slip may still be present in the submitted v8 source.
    typo = r'\chi\colon\ebinom{\Sigma^{{\leq}N}}{Y}\to r'
    fixed = r'\chi\colon\ebinom{\Sigma^{{\leq}N}}{X}\to r'
    if new_main.count(typo) == 1:
        new_main = new_main.replace(typo, fixed)
        log.append('thm:boring1 colouring-domain typo: fixed Y to X')
    elif new_main.count(typo) == 0:
        log.append('thm:boring1 colouring-domain typo: absent/already fixed')
    else:
        raise ValueError('Ambiguous copies of the colouring-domain typo')
    if f'% BEGIN {STAMP}: Section 5 markers' in validation_source:
        new_val = validation_source
        log.append('validation macros: already')
    else:
        # Appending new commands does not change the existing pinned snapshot.
        new_val = validation_source.rstrip('\n') + '\n\n' + VALIDATION_MACROS + '\n'
        log.append('validation macros: inserted')
    assert all(x.count('% BEGIN ' + STAMP + ': ' + label) == 1
               for label in REQUIRED for x in [new_main])
    return new_main, new_val, log


def diff_for(src, revised, filename):
    return ''.join(difflib.unified_diff(
        src.splitlines(keepends=True), revised.splitlines(keepends=True),
        fromfile='a/' + filename, tofile='b/' + filename))


def find_tree(root):
    roots = [p.parent for p in root.rglob('main.tex')
             if (p.parent / 'validation.tex').exists()]
    if len(roots) != 1:
        raise ValueError(f'Need exactly one main.tex + validation.tex pair; found {len(roots)}')
    return roots[0]


def process_tree(tree, apply=False):
    main = tree / 'main.tex'
    val = tree / 'validation.tex'
    a, b = main.read_text('utf-8'), val.read_text('utf-8')
    aa, bb, log = annotate(a, b)
    patch = diff_for(a, aa, 'main.tex') + diff_for(b, bb, 'validation.tex')
    if apply:
        main.write_text(aa, encoding='utf-8')
        val.write_text(bb, encoding='utf-8')
    return patch, log


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--root', type=Path)
    group.add_argument('--archive', type=Path)
    ap.add_argument('--apply', action='store_true', help='write edits into --root')
    ap.add_argument('--output', type=Path, help='write edited .tgz when using --archive')
    ap.add_argument('--patch', type=Path, help='where to write git-style unified patch')
    args = ap.parse_args()
    if args.root:
        if args.output:
            ap.error('--output requires --archive')
        patch, log = process_tree(find_tree(args.root), apply=args.apply)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            t = Path(tmp)
            with tarfile.open(args.archive, 'r:*') as archive:
                # A manuscript source archive is untrusted: restrict extraction
                # to regular files/directories, prohibiting links and traversals.
                for member in archive.getmembers():
                    target = (t / member.name).resolve()
                    if not target.is_relative_to(t.resolve()):
                        raise ValueError('Unsafe archive path: ' + member.name)
                    if not (member.isfile() or member.isdir()):
                        continue
                    archive.extract(member, t, filter='data')
            patch, log = process_tree(find_tree(t), apply=bool(args.output))
            if args.output:
                with tarfile.open(args.output, 'w:gz') as out:
                    for child in sorted(t.iterdir()):
                        out.add(child, arcname=child.name, recursive=True)
    if args.patch:
        args.patch.write_text(patch, encoding='utf-8')
    print('\n'.join(log))
    print('Unified diff lines:', len(patch.splitlines()))
    if not args.apply and not args.output:
        print('Read-only: supply --apply or --output to change manuscript bytes.')
    if args.patch:
        print('Patch:', args.patch)

if __name__ == '__main__':
    main()
