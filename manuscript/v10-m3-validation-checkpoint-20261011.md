# V10 M3: finite clone projection and canonical-input bridge

This is a proof-development and validation note. The author's V10 main
TeX remains frozen; only the ninth managed validation TODO has changed.

## Checked at exact GitHub heads

- PR 230 `4ce48cbf`: full Lean and focused V10 build/axiom audit passed.
  `MiddleCloneLData.irred_copy_projects` and
  `MiddleCloneLData.avoidance_of_deletion` prove finite **L-only**
  irreducible clone projection. Both directed present/absent relations,
  unary/diagonal atoms and singleton forbiddens are covered.
- PR 231 `d9eab742`: full Lean and focused V10 build/axiom audit passed.
  `correctedB3_of_middle_clone` derives finite L-age B3 under
  explicit clone-atomic identities at a **fixed** cut d.
- PR 232 `bcc4e683`: full Lean and focused V10 audit passed.
  Earlier terminal Sigma-letter repetition gives upper terminal pairs,
  loops/unary/diagonal data.
- PR 233 `b2f7e6fc`: focused V10 audit passed.
  Earlier canonical shortened parameter gives both lower directed
  pairs below d and zero crossing pairs at/above d. The unrelated
  full library workflow was not required to import this optional
  module and should not substitute for the focused proof audit.

## New staged proof stack — not yet certified

- PR 234: full initial ordinary clone L-column from actual letter,
  positive shortened parameter and valid new column; empty cut handled
  without inventing a level-zero parameter. An initial elaboration
  error identifying Fin.last with the explicit top coordinate was
  repaired identically on the stacked branches; retest pending.
- PR 235: the clone's free cut d depends on the source socle S0.
  A globally fixed d would be an unjustified strengthening.
- PR 236: derive corrected B3 from the canonical record inputs for
  each f(T), with source-dependent cuts.
- PR 237: recover the new cut from equality of the actual canonical
  empty/singleton parameter lists, including the d=0 case.
- PR 238: repeated canonical parameter/letter record inputs of the
  old n-crossing and new ell-crossing imply corrected B3.
- PR 239: identify these complete record inputs in actual
  IsCanonicalKptStep witnesses. All are pending exact-head Lean/axiom
  verification; none is labelled GREEN.

## Remaining M3 application

The manuscript's M3 chooses an earlier coordinate n and, for each
level-ell source type T, forms a new successor using exactly the
canonical p,c of its n-th crossing. Still required:

1. Construct this f on all intended admissible T; prove its successor
   is always admissible, rather than postulating existence.
2. Establish B1 and B2 in the full L+ normalized representation,
   with compatibility on ordinary socles only.
3. Identify old/new canonical inputs using actual Kpt successor
   graphs; apply the proved finite B3 projection through PR 239.
4. Invoke the already-verified prescribed boring extension to obtain
   the M3 ShapeMap, and check its precise duplication clause.

M2 corrected-B3 necessity/decomposition, I3 finite-L signatures,
language adapter, and final upper bound are separate open obligations.

## Safeguards

Keep one fixed distinguished source n but **not** one fixed free cut
across unrelated compatible classes. Finite B3 witnesses are pure
ordered L-structures, never E-partial structures. Preserve all original
TeX prose, four earlier mathematical repairs, and every author TODO.
