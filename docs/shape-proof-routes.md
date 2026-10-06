# The two shape Ramsey proofs

## Shared induction, separate one-dimensional inputs

`ShapeFiniteInduction` contains three proof-independent steps:

- `shapeRamsey_one_relative_of_oneDimensional` pulls a colouring back along a
  prescribed frozen-prefix subspace.
- `shapeRamsey_approximations_of_oneDimensional` performs the finite-dimensional
  induction using canonical-prefix factorisation and finite-front fusion.
- `shapePreservingRamsey_of_oneDimensional` converts the result to the paper's
  `AM H n k` coordinates.

The first step asks for one-dimensional homogeneity at the chosen cut. The
induction asks for it at every cut: a prefix's canonical coordinate can end at
an arbitrarily later source level. This is an input to the shared proof, not an
extra hypothesis of either public theorem.

`ShapeFiniteRamsey` supplies `shapeOneDimensionalRamsey` from the direct large-set
fusions. `ShapeEllentuckRamsey` supplies
`FatTree.shapeOneDimensionalRamsey_viaFatEllentuck`. The latter colours the next
row after an identity stem and applies fat-tree Ellentuck. The geometric
one-row realisation ensures that every algebraic one-dimensional coordinate is
included, not just selected replay rows.

Do not infer independence from imports. Shared structural modules also expose
the direct input. `scripts/CheckShapeProofRoutes.lean` follows the elaborated
project proof dependencies, requires the intended input, and rejects use of the
other route's one-dimensional theorem. It separately prints the transitive
axioms, including dependencies outside this project. Statement examples protect
the unrestricted natural-number parameters, frozen-prefix conclusion, and the
two finite-corollary quantifier orders.

## Correspondence and the manuscript convention

`FatTree.ShapeCorrespondence` defines initial products (`partialMap`) and
interval products (`intervalMap`). Their equality at starting index zero is
`intervalMap_zero_start`. The limit equality
`tailMap_zero_eq_associatedMap` expresses the manuscript's convention
`F_U = F_U^0`; `tailMap_ofShapeMap` gives the widening assertion with precisely
that convention.

`FatTree.ShapeRealization` proves the forward local realisation used by the
Ellentuck route. Its full successor-lift certificate is stronger than mere
last-level range containment. This does not supply an inverse-closure property
for the distinguished monoid or the stronger neighbourhood projection used by
the manuscript's separate composition-space topological theorem.

## Finite terminal levels

`ShapeFiniteBounds` provides bounded/exact approximation types and finite
composition. `ShapeFiniteCorollaries` gives compactness through a coherent
branch of bad finite colourings, followed by exact-terminal padding.

Padding repeats one fixed M3 duplication at the original positive terminal
level, matching the manuscript's `D_t^(N-t)`. The common terminal level of the
entire tested family is essential. There is no assumption that M3 supplies a
letter at level zero; the exact-end boundary is handled separately.

The algebraic identities `MMap.levelMap_comp` and `MMap.levelMap_id` belong to
`Approximation`, not to the fat-tree correspondence, and are reused by padding.

## Guidelines for further strengthening

Preserve the distinction between coordinate depth (last relative image level
plus one) and absolute target level. Same-depth refinements fix the entire
protected source segment and leave the canonical prefix unchanged. Preserve
right-composition reduction in the relative theorem: pointwise prefix agreement
alone is not the fusion conclusion.

Keep the source-letter dichotomy at the fixed cut. The unconditional A4 endpoint
must not acquire a pruning, good-pair, saturation or local-pigeonhole premise.
The common tail's full-level reduction certificate and its tracewise replay
identities are separate invariants; bottom profile entries are not equality
certificates for successor codes.

The historical direct-proof audit remains in `shape-ramsey-audit.md`. Its
snapshot-specific omissions are not a description of the current endpoints.
