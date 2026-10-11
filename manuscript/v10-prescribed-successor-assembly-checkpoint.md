# V10 prescribed successor assembly — verification boundary

Continuation of the checked order-transport and weak-crossing checkpoint (PR #225).
**Frozen author prose is unchanged.** This file is a cumulative verification note,
not a replacement for the existing managed manuscript TODO.

## Independently verified inputs

The following branches passed the **full Lean** and **focused V10 axiom audit**:

- PR #218 at `994c8614746b0fb317a76c5fa0a3073b88de4bf2`:
  `prescribedKptSkip_agrees_on_source`, based on *complete* L+ equality
  of the finite source insertion (including auxiliary E).
- PR #223 at `c3328567d573c15bc7bc392ad6d306d16ae91cf6`:
  `prescribedInsertPartial_terminalLetter_eq`, preserving the actual
  directed L, singleton and E data of the terminal Sigma letter.
- PR #224 at `e23e436d5ff3e76892301ef506717f92a1481f31`:
  `prescribedInsertPartial_old_type_eq` and
  `prescribedInsertPartial_parameterList_map`. The exact admissible
  old-vertex image is the selected total prescribed map. Hence the
  canonical empty/singleton parameter list is mapped correctly.

These five module files and their named axiom audit scripts were copied
unaltered to the new common branch, based on the PR225 review checkpoint.

## New successor assembly — awaiting new branch verification

- `PrescribedUpperSuccMatching.lean`:
  exact canonical successor above ell for matching prescribed sources,
  via the actual finite prescribed constructor and its already-checked
  terminal-letter/parameter transport.
- `PrescribedUpperSuccUnmatched.lean`:
  if the successor's ell-socle has no compatible prescribed input, the
  source, target and canonical old parameter all use the neutral map.
  Reuses the existing verified neutral upper successor theorem.
- `PrescribedKptShapeMap.lean`:
  combines both exact upper successor branches with the checked weak
  below/crossing law, node injectivity, equal-level preservation and
  root fixing. Also states membership in KptM and omission of ell.

**Do not mark these new endpoints GREEN until the focused named axiom
audit and full Lean CI pass.** No new assumptions were deliberately added
to the existing corrected-B3/target-admissibility framework.

## Remaining manuscript-level boundaries

Even after a successful concrete prescribed ShapeMap check,
M2 still requires the corrected-B3 necessity/decomposition argument;
M3 requires the repaired B3 test for the actual duplication
prescription. The I3/finite-L signature witness bridge and the
language normalization/nullary adapter remain independent.
The final big-Ramsey upper bound remains OPEN.

## Editorial policy

Update the existing boring-lemma machine-managed TODO only after
verification, preserving other notes, author TODOs and all unmarked
main prose. Do not reapply the four earlier source repairs or B3.
