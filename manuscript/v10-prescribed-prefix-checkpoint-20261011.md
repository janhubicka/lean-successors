# V10 prescribed gap insertion: review checkpoint (11 October 2026)

## Dependencies and scope

Stacked draft proofs: PR #215 (prefix transport and predecessor preservation) and PR #220 (terminal letter transport). The baseline is PR #213, whose selected matching map and representation adapter are already checked. The cumulative review notes are in this branch. No prose in the author manuscript and none of the four earlier mathematical repairs or B3 patch is rewritten by this review change.

## Proof boundary

- `compatibleSource_iff_of_prefix`: comparable nodes of levels at least `ell` have the same **complete** level-`ell` prefix, hence choose the same prescribed/neutral branch.
- `prescribedInsert_prefixReplica_type_eq`: actual `prescribedInsertPartial` gives identical complete inserted records in a model and a one-filler prefix replica, by constructor-level independence.
- `matchingKptImage_prefix_le`: use a shared admissible prescribed target and **one** valid E-cut. For the smaller node use the finite prefix replica; for the larger use the original realization. The representation adapter identifies both with the unique selected images.
- `prescribedInsertPartial_type_below_gap`: no inserted coordinate enters the short record, so every old L and E atom is copied.
- `prescribedKptSkip_prefix`: decompose below/below, above/above (common branch), and crossing (prescribed/neutral).
- `prescribedInsertPartial_terminalLetter_eq`: old pair terminal letters are unchanged by a **non-neutral** prescribed insertion, including both binary orientations, unary/diagonal data and auxiliary E pairs.

## Independent adversarial checks

1. Source compatibility is checked on the complete level-`ell` type, not only on L-reducts.
2. A representative with the shorter prefix must remain forbidden-free; use the already proved prefix replica age lemma.
3. Do not postulate an equal canonical E-cut; extract one from admissibility of the prescribed target and use uniqueness.
4. No change of the distinguished type-vertex index is identified at the level of physical vertices; only equality of full extracted records is claimed.
5. Deleting the inserted coordinate to recover the source does **not** by itself prove monotonicity, but the explicit finite prefix proof addresses this.
6. Global successor preservation does **not** follow merely from prefix and old-letter transport: the mapped empty-or-singleton parameter list must be identified with the new canonical parameter.
7. The source-edge crossing the inserted level must use the **weak** successor conclusion; the exact upper-gap equality holds only above it.
8. The normalized Boolean finite `L^+` model has a separate language-adapter obligation. M2's necessity of B3, M3's duplication age, and I3's signature witnesses are unchanged and open.

## Current verification status

The PRs contain Lean source and `#print axioms` scripts for the new endpoints. Keep the corresponding manuscript marker **UNDER LEAN AUDIT**, not GREEN, until the exact heads pass full Lean, focused V10 audit and axiom inspection. If a failure is found, repair the Lean source on its own proof PR without strengthening the hypotheses.

## Next targets

(1) Exact agreement with the prescribed partial map `F.target` on `F.source`: use the already checked `upper_realizes_target_L` for the full L-reduct, and prove the E-column equality separately from admissibility and canonical E-cut data; avoid the erroneous shortcut from L equality to L+ equality.

(2) Image of the old canonical parameter vertex under the prescribed-or-neutral total map, again using the selected-image representation adapter, and the empty-or-singleton parameter list equality.

(3) Above-gap exact successor transport by the actual canonical decomposition; one weak crossing case; then construct `ShapeMap` and prove membership in `KptM` and omission of level `ell`.

Do not certify the full boring lemma, M2, M3, I3 or the paper's upper bound from these local facts.
