# lean-successors

Lean 4 verification project for **Ramsey theorem for trees with successor operation**
(Balko–Chodounský–Dobrinen–Hubička–Konečný–Nešetřil–Zucker).

The project starts at the combinatorial core of Section 3.1: the support
bookkeeping and the Hales--Jewett-based one-dimensional pigeonhole lemma.

## Verified so far

The following layers are checked by Lean/CI on branch
`formalize-hales-jewett`.

1. **Starred combinatorial lines** (`SuccessorTree/StarLine.lean`):
   `L(a)`, `L(*)`, prefix, concatenation, and constant-prefix lemmas.
2. **Successor-pigeonhole support** (`SuccessorTree/Support.lean`,
   `SuccessorTree/Pigeonhole.lean`):
   the paper's support word containing every transition and the abstract
   Hales--Jewett replay argument. The tree-specific replay equations are
   isolated in `ReplaySystem`.
3. **Variable words and Shift** (`SuccessorTree/HalesJewett/VariableWord.lean`):
   infinite variable words in block normal form and
   `Shift(W,n)(u⌢v)=u⌢W(v)`.
4. **Subspace composition** (`SuccessorTree/HalesJewett/Composition.lean`):
   `(W(U))(v)=W(U(v))` and the combined Shift/substitution identity.
5. **Combinatorial-forcing plumbing** (`SuccessorTree/HalesJewett/Forcing.lean`):
   largeness, avoiding subspaces, the two pullback observations, and the
   binary-to-finite-colour refinement by nested subspaces.
6. **Reduction layer** (`SuccessorTree/HalesJewett/ForcingReduction.lean`):
   once the large-set proposition is available, the binary and finite-colour
   omega-dimensional statements, and hence the starred line needed by the
   successor pigeonhole, follow formally.

## Non-precompact colourings

The library also contains the formalised lower-bound arguments used by the
BANANA project:

* odd subset-sum surjectivity for pre-BANANA and Folkman--BANANA;
* affine-fibre parity over `F₂` and the determinant/Cauchy--Binet step;
* the residue group algebra and the full bilinear residue-count theorem;
* target-copy wrappers showing that the selected pre-BANANA blocks are
  legitimate, the Folkman witness has odd ordinary count, and the BANANA
  affine slice produces nonzero vectors with the required pairing parity;
* coordinate perfect-copy interfaces turning the BANANA matrix data into
  injective left/right linear maps preserving the pairing, and identifying
  the matrix weight with the ordinary support-intersection count of the
  ambient image vectors.

These results live under `SuccessorTree/NonPrecompact/`.

## Hales--Jewett dependency

The proof in `janhubicka/Hales-Jewett-by-combinatorial-forcing` is an
**induction on alphabet size**. Its large-set Proposition 1 is proved assuming
the one-dimensional theorem for the same alphabet; it is not an unconditional
replacement for Hales--Jewett. Lean makes this dependency explicit.

The remaining combinatorial work is therefore:

* formalize Lemma 1 (large set contains a line) under the same-alphabet
  one-dimensional hypothesis;
* formalize Lemma 2 and the fusion limit;
* derive Proposition 1;
* formalize the finite-colour alphabet-increase step from the
  omega-dimensional theorem on the smaller alphabet;
* close the alphabet-size induction and obtain `StarHJ` without any
  Hales--Jewett black box.

The accompanying proof audit is in
`docs/hales-jewett-proof-audit.md`. The source corrections are in
`janhubicka/Hales-Jewett-by-combinatorial-forcing#1`.

## After Hales--Jewett

We return to the successor-tree structure:

* formalize the successor operation S1--S3;
* shape-preserving maps and their basic support lemmas;
* M1--M3, shape splitting, and canonical extension;
* instantiate `ReplaySystem` from M3;
* continue to fat subtrees, A4, and the main theorem.

## Build

```bash
lake update
lake exe cache get
lake build
```

CI executes these steps on every push and pull request. The project pins
mathlib to commit `5bd58ac291422a21f412ae354c91e7d172255a2c` and Lean
`v4.35.0-rc3`.
