# successor-tree-lean

Lean 4 verification project for **Ramsey theorem for trees with successor operation**
(Balko–Chodounský–Dobrinen–Hubička–Konečný–Nešetřil–Zucker).

The project starts at the combinatorial core of Section 3.1: the support
bookkeeping and the Hales–Jewett-based one-dimensional pigeonhole lemma.

## Current milestone

The first milestone deliberately separates three layers.

1. **Starred combinatorial lines** (`SuccessorTree/StarLine.lean`).
   `L(a)` and the truncation `L(*)` are defined and basic prefix/concatenation
   lemmas are proved.
2. **Support bookkeeping** (`SuccessorTree/Support.lean`).
   For a finite alphabet we construct a word containing every letter and prove
   that Hales–Jewett can be applied after this prefix, yielding a line whose
   `L(*)` contains the whole alphabet.  This formalizes the paper's
   “choose a word `s` containing every letter of Γ” step.
3. **One-dimensional pigeonhole reduction** (`SuccessorTree/Pigeonhole.lean`).
   The Hales–Jewett part of the proof is complete modulo two explicit inputs:
   * `StarHJ`, the starred Hales–Jewett theorem itself;
   * `ReplaySystem`, the structural replay equations produced in the paper by
     canonical extension plus M3 duplication.

Nothing tree-specific is hidden in `StarHJ`.  Conversely, `ReplaySystem` does
not contain any Ramsey statement: it only records the two equations that the
paper proves for the constructed block `h`.

## Next verification steps

We first discharge the combinatorial input using the proof in
`janhubicka/Hales-Jewett-by-combinatorial-forcing` (audit in
`docs/hales-jewett-proof-audit.md`):

* formalize variable words, substitution, `Shift`, and fusion limits;
* formalize the large-set forcing lemmas and alphabet-size induction;
* prove `StarHJ` with no Hales--Jewett black box;

Then return to the successor-tree layer:

* formalize finite rooted levelled trees and the successor operation;
* formalize shape-preserving maps and finite approximations `AM`;
* prove the basic support lemmas (successor/order/meet preservation);
* formalize M1–M3 and canonical extension;
* instantiate `ReplaySystem` from M3, thereby obtaining the paper's
  one-dimensional pigeonhole lemma with only `StarHJ` remaining as an input;
* formalize the finite starred Hales–Jewett theorem and discharge `StarHJ`;
* continue to fat subtrees and A4.

## Build

```bash
lake update
lake build
```

CI runs the same build on every push and pull request.  The project pins
mathlib to commit `5bd58ac291422a21f412ae354c91e7d172255a2c`, whose
`lean-toolchain` is Lean `v4.35.0-rc3`.
