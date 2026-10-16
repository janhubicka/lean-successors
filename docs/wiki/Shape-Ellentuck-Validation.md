# Theorem 1.11: use the fat-tree projection, not direct A.3(2)

**Corrected strategy (16 October 2026):** the original paper
introduces fat trees precisely because the approximation space
of shape-preserving maps need not satisfy Todorčević A.3(2).
Trying to prove A.3(2) unconditionally for that direct space
is therefore not a viable validation route.

The concrete fat-tree space *does* satisfy A.1–A.4,
Tychonoff closedness, and the topological Ellentuck theorem,
all already checked in Lean (`FatTree.fatTreeEllentuck`).
The remaining Theorem 1.11 proof obligation is the **projection
and neighborhood transfer** in Section 4, not another fat-tree
pigeonhole argument.

## Original map and the missing bridge

Let `π(U) := FatTree.associatedMap H U`.
The source proves surjectivity (Observation 2.8), implemented
by `FatTree.associatedMap_ofShapeMap`. It claims in Lemma 4.1:

```text
π([x,U] in fat trees) = [F_x,F_U] in the M-map space.
```

This formula needs actual proofs of:
(a) factoring the projections of geometric refinements by
right-composition, (b) compatibility of finite fat-tree stems
with projected finite M-map approximations, (c) lifting
arbitrary right factors while preserving **literal** fat
stems, and (d) realizing arbitrary monoid prefixes by such
fat stems with the correct source/target depth.

The currently proved range fact `F_U ≤° U` is a geometric
containment. It does not by itself supply the algebraic
right factor `F_V = F_U ∘ G` for `V ≤_fat U`.
Also, replacing the first rows of a newly constructed fat
refinement by `x` must preserve its oneLift inclusions.
That is not automatic from equality of partial projected maps.

In the continuity argument, inverse images of monoid basic
neighborhoods must be open around **each actual fat-tree
point in the inverse image**; global surjectivity is not
enough. The claimed union of fat basics assumes this
fibrewise lifting property.

## The genuinely verified pieces

- Fat-tree typed A.3(2), A.4, and full Ellentuck:
  `FatTree.A3Typed`, `FatTree.A4ReviewComplete`.
- Canonical projection and widening:
  `FatTree.ShapeCorrespondence`, with
  `associatedMap_ofShapeMap`.
- One-row *forward* realization inside fat trees:
  `FatTree.ShapeRealization.tailCoordinateRow_oneBlockOccurs`.
- The direct M-map approximation A.1/A.2/A.3(1), plus
  the separately verified M1 Tychonoff closedness.
  These are useful results but **do not** repair the failure
  of direct A.3(2).

## Original topological transfer after the bridge

If `π` is shown to be a continuous open surjection, and
each required monoid basic neighborhood `[f,F]` has a
fat stem lift `[x,U]` of matching depth satisfying the
exact neighborhood image formula, the proof is standard:

1. Continuous and open maps pull back nowhere dense
   subsets to nowhere dense subsets; hence meagre sets
   to meagre sets and Baire-property sets to Baire-property sets.
2. Lift `[f,F]` to `[x,U]`, and apply the verified
   fat-tree Ellentuck theorem to `π⁻¹(X)`.
3. Project a fat-tree homogeneous refinement `[x,V]`
   to the whole shape-map neighborhood `[f,π(V)]`,
   preserving its required depth.

This proves Theorem 1.11 *if and only if the missing
lifting/projection claims are supplied in the needed form*.
It does not introduce direct A.3(2) into the assumptions.

## Validation status

Theorem 1.11 remains **OPEN**, while the fat-tree
Ellentuck Theorem 1.17 and finite-dimensional
shape-preserving Theorem 1.6 are **CHECKED**.
The current Lean work is PR #560, which isolates the
projection obligations and attempts the finite-prefix
part directly from the canonical row products.
See the full [adversarial transfer audit](Fat-Tree-to-Shape-Map-Transfer.md).

The printed Ramsey-null proof must avoid `[f,F_V]`,
not `[n,F_V]`. Also ensure the last-image-level
convention and finite approximation length `d+1`
are not confused when identifying `depth_U(x)`.
