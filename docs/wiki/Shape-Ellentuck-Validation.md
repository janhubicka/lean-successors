# Theorem 1.11: direct monoid Ellentuck validation

This page separates the genuine **shape-map monoid** topological
Ramsey-space conclusion of the manuscript from the already verified
**fat-tree** Ellentuck theorem and its finite-dimensional
shape-Ramsey corollary. Those are different topological spaces.

The manuscript defines the monoid's basic neighborhoods by
`[f,F] = {F ◦ G : G ∈ M, F ◦ G extends f}`
(Definition 1.9). In its printed Lemma 4.1, the projection
`π : FatTree → M`, `U ↦ F_U`, is claimed continuous and open,
using the exact identity `π[[x,U]] = [F_x,F_U]`.
The reverse inclusion (lifting arbitrary right factors while
preserving a prescribed fat-tree prefix) is **not** a consequence
of mere surjectivity `associatedMap_ofShapeMap`, and has
**not** been exported as a checked theorem.

## Available direct M-map Ramsey-space infrastructure

The source already defines the *actual* M-map refinement relation,
`RamseyReduction H F G := ∃ K ∈ M, F = G ∘ K`, and finite approximations
in `SuccessorTree.RamseySpace.Basic`. Rather than silently identifying
fat-tree and monoid neighborhoods, use this direct approximation system
as the target for a source-faithful proof:

| Todorčević prerequisite | Lean endpoint | Status |
| --- | --- | --- |
| A.1 (separation, coherent finite approximations) | `SMTree.ramseyApproximationSystem` | Proved |
| A.2 finitarization, finite lower cones, right-composition recovery | `SMTree.ramseyFinitization` | Proved |
| A.3(1) nonempty compatible refinement neighborhoods | `SMTree.fusionNeighborhood_nonempty` | Proved |
| Tychonoff closed approximation image | `SMTree.ramseyApproximation_isTychonoffClosed` | New proof candidate, exact-head CI required |
| Fusion completeness | `SMTree.ramseyApproximation_fusionComplete` | Follows from new closedness + A.2; CI required |
| A.3(2) **amalgamation refinement** | No unconditional direct M-space theorem | **Open** |
| A.4 **one-step pigeonhole at arbitrary stems** | No unconditional direct M-space theorem | **Open** |
| Full source Theorem 1.11 | Needs A.3(2), A.4 and theorem-level conclusion | **Open** |

The new closedness proof is short and uses M1 alone. Given a coherent
sequence of finite approximations whose every finite prefix is
realized, choose realizing total monoid maps of progressively greater
length. The choices agree on every frozen level; the existing
`ShapeMap.fusionLimit` is a valid shape map, and
`SMTree.fusion_mem` puts it back in M. Its finite restrictions
reproduce the code. The published Tychonoff formulation then follows
from the proved
`isTychonoffClosed_iff_isClosedApproximationImage` in
`lean-ramsey-space-todorcevic`. A.2 plus closedness gives fusion
completeness without A.3 or A.4.

## The two remaining mathematical obligations

**A.3(2) (refinement).** Let `S = ramseyApproximationSystem H`
and `fin = ramseyFinitization H`. For a finite approximation
`a : S.Approx n`, `B : MMap H`, its depth
`d`, and any `A ≤ B` with `[a,A] ≠ ∅`,
construct `A' ∈ [d,B]` such that
`[a,A'] ⊆ [a,A]`.
The verified `fusionNeighborhood_nonempty` proves only
A.3(1), not this refinement. A candidate construction should
combine M2's genuine *last skipped level* factorization and the
canonical finite extension, without assuming geometric fat-tree
reduction is identical to algebraic right composition.

**A.4 (pigeonhole).** For the same stem and ambient point, and
*every* two-colouring of one-step approximations
`S.oneStepApproximations a B`, find
`A' ∈ [d,B]` for which the **entire** one-step front is monochromatic.
The verified direct `shapeOneDimensionalRamsey` and the alternative
fat-tree one-block proof may supply the combinatorial input, but
a source-faithful argument must also prove the precise correspondence
between those one-block coordinates and *all* M-space extensions
at arbitrary `a`.

Once both hold, construct
`RamseySpace.AbstractRamseySpace (ramseyApproximationSystem H)`
from its verified finitarization and use
`RamseySpace.abstractEllentuck_textbook` with Tychonoff closedness.
This proves the actual monoid Ellentuck statement without needing
the stronger projection identity of printed Lemma 4.1.

## A second possible route: verify the projection identity

An alternative is to formalize both inclusions of
`π[[x,U]] = [F_x,F_U]` plus the continuity/openness claims.
The current `FatTree.ShapeCorrespondence` checks
`associatedMap_ofShapeMap` (surjectivity) and forward
local one-row realizations, **not** this exact inverse-neighborhood
lifting theorem. A source/referee review is required for the
compatibility of arbitrary right factors `F_U ∘ G` with a fixed
finite fat-tree stem `x`; replacing the stem after building the
tail must preserve genuine fat-tree reduction.

## Indexing and manuscript correction notes

For a nonempty finite approximation with last represented source level
`d`, the direct Ramsey-space approximation index is `d+1`.
Level zero of its approximation system is the unique *empty*
approximation. Depths and the source's `-1` empty approximation
convention must be matched explicitly.

In the printed null-set paragraph following Lemma 4.1, the avoided
neighborhood must be `[f,F_V]`, not `[n,F_V]`.
Do not promote the validated fat-tree Theorem 1.17 to the monoid
Theorem 1.11 without completing one of the two routes above.
The finite-dimensional Theorem 1.6 is fully checked and independent
of the missing topological step.
