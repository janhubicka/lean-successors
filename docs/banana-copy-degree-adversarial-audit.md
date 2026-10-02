# Adversarial audit: BANANA copy-Ramsey-degree layer

Scope: `SuccessorTree/NonPrecompact/CopyRamseyDegree.lean`.

This audit is deliberately separate from the proof implementation.  It checks
the quantifiers and the translation between the residue obstruction and the
copy Ramsey degree used in the circulation manuscript.  GitHub runners are not
used for this branch; compilation status must therefore be recorded separately
from the mathematical audit.

## Referee pass A: quantifier order

For fixed ambient `C`, exponent `k` and source pairing `b`, the
colouring is defined from the one fixed perfect completion of `C`.
It is chosen before any target embedding.  The theorem
`exists_completionResiduePersistentColouring` then quantifies universally
over every embedding of the perfect target into `C`, and universally over
every one of the `2^k` colours.  Thus no coordinate completion or colouring
is allowed to depend on the later target copy.

Assume a finite copy-degree bound `t`.  Put `k=t` and use the perfect
target of dimension `2^(k+1)`.  The degree hypothesis first supplies an
ambient structure `C`; only then do we choose its fixed-completion
colouring.  The degree hypothesis supplies a target embedding on which at
most `t` colours occur, while persistence says that the same embedding
contains all `2^k` colours.  Since `t < 2^t`, this is a contradiction.
The edge case `t=0` is included: the palette has one colour.

No existence of an embedding is smuggled into the lower-bound argument.  If
the degree witness failed to contain the chosen target, it would already fail
the definition of degree at most `t`; in the contradiction proof the
embedding is supplied by the degree hypothesis itself.

## Referee pass B: copies and colours

A `BananaLinePairCopy A b` is exactly the range data of a copy of the
four-element source `A_b`: one nonzero left vector, one nonzero right
vector, and pairing `b`.  Over `F₂` there is only one nonzero vector in
each one-dimensional source sort, so no extra basis choice or source
automorphism remains.  `mapLinePairCopy` uses injectivity to preserve
nonzeroness and pairing preservation to preserve `b`.

The completion-intersection residue of every such copy has parity `b`.
The subtype `ResidueParityColour k b` therefore contains exactly the
possible colours.  Its cardinality is `2^k`, and
`residueParityColourEquivFin` merely enumerates this finite set by
`Fin (2^k)`; it does not identify or discard colours.

For the sharper pairing-one statement, a residue `z` of parity one has
an odd canonical representative `z.val`.  The existing
`exists_pairingOne_completionIntersectionColour` theorem applies to that
representative, and casting `z.val` back into the residue ring returns
`z`.  Hence the target dimension `2^(k+1)-1` already realises the full
odd palette.

## Referee pass C: dimensions and boundary cases

The general target dimension is written
`((2^(k+1)-1)+1)` because this is the normal form inherited from the affine
slice theorem.  Since `2^(k+1)>0`, it is exactly `2^(k+1)`, the manuscript's
`B_q` with `q=2^(k+1)`.  The sharper target for pairing one has dimension
`2^(k+1)-1=q-1`.

The parameterisation covers every power of two `q>=2`: write
`q=2^(k+1)`.  At `k=0`, the general target is two-dimensional, the
pairing-one target is one-dimensional, and the palette has one colour.
Nothing in the proof requires `k>0`.

## Remaining interface boundary

The file works in the chosen-basis `BananaMatrixStructure` presentation
already used by the formalised completion and persistence theorems.  A
line-pair copy is represented directly by its range vectors rather than by a
separate quotient of one-dimensional embeddings by source automorphisms.
For `F₂` these notions coincide for the rigid sources `A_0,A_1`, as
explained above.  If a later general-purpose library of finite-structure
copies is introduced, this identification should become an explicit
equivalence rather than remain an interface observation.

## Verification status

The mathematical implication and all quantifier boundaries above have been
checked twice independently as proof reviews.  The branch intentionally uses
`[skip ci]` because project runners are unavailable.  Do not mark the
circulation theorem as machine-checked until this new file has been compiled
against the pinned Lean/mathlib toolchain.
