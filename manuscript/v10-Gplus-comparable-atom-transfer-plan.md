# Successor v10 — comparable G+ atom transfer

15 October 2026. Research/validation note only, not a Lean certificate or an edit
to the author's circulated proof. Target: the exact induced L+ action in
Observation 6.42, after the current cap-prefix candidates pass their CI.

## Checked prerequisites

- `gPlusShapeImage_injective`, `GPlusRepresentingPair.image_vertex_eq_iff_vertex_eq`: PR #478 full Lean/axiom verified.
- `shapeImageRetainedCode_eq F B`: PR #477 full Lean/axiom verified.
- `shapeImageRetainedIndex` and the exact last-coordinate identity: PRs #475 and #482, the former verified, the latter candidate.
- `FiniteGPlusVertex.canonicalCap_le_of_prefix` and
  `gPlusShapeImage_properPrefix_iff`: PRs #480/#481, candidates.

## The exact comparable-pair calculation

Suppose `hAB : A.IsProperPrefix B`. Let `hImg` be the proper-prefix
image statement (PR #481). Use the source coordinates

    p := A.lowerLastIn B hAB    -- Fin B.val.size, value |A|-1
    q := B.last                 -- Fin B.val.size, value |B|-1

and their image counterparts

    p' := (gPlusShapeImage F A).lowerLastIn
            (gPlusShapeImage F B) hImg
    q' := (gPlusShapeImage F B).last

as indices in the complete image code of B.

By the checked size equality for the G+ image,

    |Phi_F(A)| = lambda(|A|-1)+1,
    |Phi_F(B)| = lambda(|B|-1)+1,

so `p'.val=lambda(p.val)` and `q'.val=lambda(q.val)`.
Both are literal Fin equalities by `Fin.ext`, with the proof
bounds discharged by the existing strict level-map theorem.

The verified reconstruction

    shapeImageRetainedCode F B = B.val

must be evaluated at `p,q` in all four tables. Use generic
`FinitePartialCode.binary_eq_of_eq` and
`FinitePartialCode.E_eq_of_eq` congruences to avoid illicit
dependent projections of code equalities. This yields the exact
directed and E-bit identities:

    Phi_F(B).binary p' q' t = B.val.binary p q t
    Phi_F(B).binary q' p' t = B.val.binary q p t
    Phi_F(B).eRelation p' q' = B.val.eRelation p q
    Phi_F(B).eRelation q' p' = B.val.eRelation q p.

In particular these are equalities of Bool, preserving false as
well as true. The two directions are distinct and must not be
identified. Apply `finiteGPlusBinary_forward/reverse` and
`finiteGPlusE_forward`, plus the corresponding reverse E
unfolding lemma, to obtain both ordered-pair action identities.

## Equal and incomparable pairs

For `A=B`, the off-diagonal directed binary and E interpretations
in G+ are false, because no strict prefix comparison can hold.
Diagonal binary-loop atoms are stored separately, and their exact
preservation is addressed by PR #482.

For `A,B` incomparable in the proper-prefix order, use both directions
of PR #481's `gPlusShapeImage_properPrefix_iff` to show that their images
remain incomparable. `finiteGPlusBinary_incomparable` and
`finiteGPlusE_incomparable` then give false for both orientations.
This proves absence-reflection, not merely a homomorphism.

Unary predicates and separate diagonal binary atoms are evaluated at
the last coordinate of each single G+ code and are handled by the
candidate `gPlusShapeImage_preserves_unary/diagonal` of PR #482.

Once all these cases pass the transitive standard-axiom audit,
`gPlusShapeImage F` is an induced L+ embedding of the unordered
G+ structure (and respects the code-prefix tree). Combined with
the checked identity, composition and representative equality,
this will complete the finite relational part of Observation 6.42.

## Important order caution

An arbitrary size-nondecreasing enumeration of ALL G+ vertices has
arbitrary tie-breaking within one size layer, so the induced shape
action need not preserve that arbitrary tie order globally.
The final ordered copy used in Theorem 6.26 lies on the strict
size-increasing prefix chain of the concrete H+ embedding.
On this copy, the common strictly increasing level map suffices
to preserve the required order. Do not silently strengthen the
statement to a globally order-preserving G-omega self-map.

## Remaining after Observation 6.42

The actual Algorithm 5.4 envelope must cover the chosen represented
finite G+ vertices (not just satisfy the numerical bound).
Then verify the precise finite approximant domain for the finite
palette, repeated successor Ramsey colour stabilization, and
composition with the genuine ordered embeddings K→H→G^omega→K.
Theorem 6.26 must remain marked incomplete until that assembly is
Lean-checked. Keep the original manuscript prose frozen; add only
review-only TODO and accurately scoped validation markers.
