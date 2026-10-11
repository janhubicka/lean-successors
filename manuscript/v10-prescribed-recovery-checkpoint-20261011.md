# V10 prescribed-map recovery and injectivity checkpoint

11 October 2026 UTC. Continuation from PR210,
`37d89785fe6cdfd5de97fe29f5582edac5220b1b` in
`janhubicka/lean-successors`.

**Verified:** complete old-record recovery, a common raw left inverse of
`prescribedKptSkip`, node injectivity including mixed branches, and the
arbitrary-finite-representation adapter for selected matching images.
**Not yet verified:** agreement with f, all predecessors, or the prescribed
ShapeMap and final big-Ramsey upper bound.

## Exact proof checkpoints

| PR | Head | Full Lean | Focused build and axiom audit |
|---|---|---|---|
| 211 | `55276dc4dc5cb6f0df20d551bcea2d2a97078e67` | `38100205697`: success | `38100205700`: success |
| 212 | `203422b47a71b91c60f9fb1daafe21719e8d6ee8` | `38100408373`: success | `38100408422`: success |

Both PRs are draft and unmerged. The separate annotation branch is
`review-v10-prescribed-recovery-notes-20261011`; it retains the same Lean
source as the checked PR212 tree.

The synthetic PR merge commits `e90d5e6d183fdd24a2e7cf2fa6f4ccaaad2122b6`
and `4e44351ceb1d88bc8fe36c27c1ccceeb7debd20f` were compared with the
corresponding heads. Both comparisons have no changed files, so these
checkout trees do not introduce unreviewed base-branch source changes.

## New formalization

`SuccessorTree/V10/InsertedTypeRecovery.lean` defines deletion of the
inserted ordinary coordinate from full L+ records and `recoverInsertedRaw`
on raw nodes. It proves recovery for the literal prescribed constructor
and the literal neutral constructor, retaining every directed positive
and absent binary atom, unary and diagonal fact, and E pair, including
the distinguished coordinate. The finite old-record recovery statement
needs no compatibility or forbidden-age premise.

`SuccessorTree/V10/PrescribedKptInjective.lean` proves the single identity

    recoverInsertedRaw ell (prescribedKptSkip ... a).val = a.val

under the existing total-map hypotheses: B1/B2 data, corrected B3,
admissible prescribed targets on the source set, and ell > 0. Applying
this identity to equal images gives `prescribedKptSkip_injective`.
There is no same-branch premise or predecessor-preservation premise.
Prescribed/neutral comparisons and comparisons across the gap are covered
by the same argument, not merely by equality of numerical levels.

Recovery is deliberately raw-valued. Admissibility after arbitrary
coordinate deletion is not asserted. On the candidate's image the
recovered raw node is the original admissible source.

`SuccessorTree/V10/PrescribedImageRepresentation.lean` first proves
`matching_constructor_avoids_of_valid_cut`. Uniqueness of the inserted
ordinary E cut identifies a supplied valid cut with the one furnished
by finite existence. Consequently avoidance for the literal constructor
at that cut is derived, not assumed. The endpoint
`matchingKptImage_raw_eq_of_representation` then computes the selected
matching image in any genuine forbidden-free finite source realization,
using any compatible prescribed source and valid canonical cut.
This is the adapter needed for the prefix-replica proof, not that proof.

## Downloaded evidence

The ten new endpoints in `CheckV10PrescribedKptInjective.lean` and the two
in `CheckV10PrescribedImageRepresentation.lean` passed the strict named
endpoint checker. All dependencies are contained in `propext`,
`Classical.choice`, and `Quot.sound`; there are no additional axioms or
`sorryAx` dependencies. The new audit scripts in the downloaded artifacts
match the submitted scripts byte-for-byte.

PR211 artifact `11687506937`, SHA-256:
`b2bde8f9e7b2573bc6e71e88c1ca932c5ca84fe3034fd252c9f31f7bb42c7257`.
PR212 artifact `11688265270`, SHA-256:
`fcb33847d78df5815f514cb6c05d33badedb01dd3e165bebe9ee56a15a3ee894`.
Both hashes were checked against the downloaded zip bytes.

All downloaded V10 report files were rechecked too: 47 logs with 512
reports at PR211, and 48 logs with 514 reports at PR212. These are audited
endpoint reports, not a claim of complete manuscript verification.

The first PR211 build rejected two arithmetic proofs because the Sigma
level had not been exposed as `A.freeLevel v`. Explicit type annotations
fixed these elaboration errors without changing any theorem statement or
adding a hypothesis. The same correction was carried into PR212. The
failed first build is retained separately as development evidence.

An independent finite regression passed 123,656 directed binary atom
checks, 269,942 old E atom checks and 570 numerical recovery checks.
This is supplementary finite testing, not a substitute for Lean. The
axiom-log checker also rejected eight deliberately corrupted reports,
including missing or substituted endpoints and extra axioms.

## Cumulative V10 annotations

Only the boring-lemma TODO is substantively updated; the first eight
managed TODOs are byte-identical to PR210. There are still nine grouped
notes. The new note marks recovery/injectivity and the representation
adapter GREEN and gives a short deletion argument for the manuscript.
Agreement, all predecessors and the exact successor identities stay OPEN.

The unchanged updater passed its local tests for both `lem:boring` and
`lem:local-age`, legacy migration, duplicate/ambiguous anchors, preservation
of unmarked prose and author TODOs, idempotence and patch application.
These are synthetic source fixtures, not a new application to a complete
author manuscript. The four earlier mathematical repairs and the separate
B3 source repair are not reapplied or rewritten.

## Next proof boundary

Use `prefixReplicaPartialStructure` for upper prefixes. Derive equality
of the ell-prefix and the common compatibility decision, then use the
new arbitrary-representation theorem and full-record independence at
the shorter cut. Handle lower prefixes by retained old coordinates.
The precise sequence is in `v10-prescribed-map-next-obligations.md`.

Agreement with the prescribed f still requires the complete L+ comparison,
not just the L reduct. Canonical successor parameters and terminal letters
remain to be transported, with the weak ell-1 -> ell crossing law kept
separate. M2's corrected-B3 necessity/decomposition step, M3's actual
duplication age test, the I3 finite-L witness reconciliation, the language
adapter and the final upper bound remain open.

## Source and execution boundary

Lean was checked by GitHub Actions, not by a local Lean installation.
The continuation bundle contains cumulative source/review changes,
an incremental patch against PR210, audit scripts and downloaded evidence.
It is not a complete repository checkout or regenerated author manuscript
archive. The current full author V10 source was not obtained in this
continuation; no fresh full-manuscript application or TeX compilation is
claimed. Earlier source-repair provenance is preserved separately.
