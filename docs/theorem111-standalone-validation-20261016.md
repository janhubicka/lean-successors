# Standalone note and validation record — Theorem 1.11

**Date:** 16 October 2026. **Status:** Complete English ZFC counterexample, manually adversarially reviewed and finite-model regression checked; not yet a complete Lean formalization.

## Standalone deliverable

The standalone typeset manuscript is titled

> **A closed nowhere-dense non-Ramsey-null set in a successor-map monoid.**

It is an eight-page LaTeX/PDF note with an abstract, definitions of the free one-parameter ancestral tree and weak-successor maps, the original monoid Ellentuck neighbourhoods, proof of the marked-map and compatibility lemmas, the CH-free transfinite recursion, the nowhere-density argument, and an appendix recording precisely how the tree satisfies (M1)–(M3).

The same complete mathematical proof is maintained in
[`docs/theorem111-zfc-counterexample-20261016.md`](theorem111-zfc-counterexample-20261016.md),
with the separate [adversarial audit](theorem111-zfc-counterexample-referee-20261016.md). The typeset PDF, TeX and validation bundle were generated as conversation artifacts for the author. The actual `main.tex` of the successor manuscript is **not** modified.

## Exact finite verification

An independent self-contained test enumerates the source free histories:
```text
PASS: 3492 exhaustive Q_A histories (level<=6)
PASS: 55080 pure-map marker tests on level<=5
PASS: 495 retained/skipped contradictory target-edge checks
PASS: pure one-gap maps fix the root and s and omit exactly one target level
```

In addition to the earlier [PR #564 workflow](https://github.com/janhubicka/lean-successors/actions/runs/38970722368), the independent script tests randomly composed pure one-gap maps under deterministic seed `1112026` and verifies the marker contradiction on intersecting target levels. These are **finite diagnostics**, not replacements for an infinitary proof.

The LaTeX manuscript passes three pdfLaTeX iterations in halt-on-error mode with no unresolved reference or overfull-box warnings, and the final eight-page A4 PDF was visually inspected.

## Independent mathematical obligations checked in the note

1. `Q_A` is a total injective weak-successor preserving map on **every** history, with image-level range `{1}∪A`.
2. At retained levels its mandatory first code is never the *root parameter* `(0)`; skipped levels are marked with `(0)`.
3. If `G(r)=s` shares a genuine **algebraic right multiple** with `H∘Q_A` and pure `H`, an infinite set `D_G^H` is contained in `A`. This is substantially stronger than a level-range intersection claim.
4. For a fixed previous `G` and pure `H`, at most **one** member of a pairwise almost-disjoint family is compatible, so a transfinite recursion of length continuum works in ZFC even if continuum is singular.
5. Any pairwise incompatible family is nowhere dense in the **right-composition monoid Ellentuck topology**, using a non-surjective late one-gap right factor fixing the finite stem.
6. The closure of the constructed transversal is closed nowhere dense but meets every pure refinement of `[f,id]`; its complement is open dense but not Ramsey.

## Honest formalization boundary

The free ancestral shape monoid **does** satisfy M1–M3 by the existing checked Lean instance `FreeAncestral.freeSMTree` and its explicit M2/M3 components. However, the new general infinite `Q_A`, all-`A` compatibility lemma, and transfinite topological construction are **not Lean-kernel certified**. The standalone paper is an English proof plus independent finite regression/audit, not a claim of Lean verification of the full counterexample. No external human-referee endorsement is represented.

The verified fat-tree Ellentuck theorem and finite shape-Ramsey theorem are unaffected; the counterexample targets the original unqualified shape-map **monoid** Ellentuck statement of Theorem 1.11.