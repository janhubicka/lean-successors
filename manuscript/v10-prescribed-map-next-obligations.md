# Prescribed total node map: remaining obligations

This is a proof-development checklist, not a completed ShapeMap proof.
The current source is the normalized Boolean L+ representation; the
separate manuscript language-normalization adapter remains open.

## Concrete map to use

Use `PrescribedBoringData.prescribedKptSkip` from
`SuccessorTree/V10/PrescribedKptSkip.lean`, not a fresh abstract map with
prefix or successor laws postulated. The inputs are the B1/B2 data,
corrected finite L-age B3, admissibility of targets on the prescribed
source set, and ell > 0. No condition is used on target values outside
that source set.

## Recovery and injectivity

`InsertedTypeRecovery.lean` defines `eraseInserted` on full L+ records and
`recoverInsertedRaw` on raw nodes. `PrescribedKptInjective.lean` proves
`prescribedKptSkip_recover` for the actual total map. The same recovery
operation applies to every matching image and every neutral image, and
fixes lower nodes. Applying it to equal images gives
`prescribedKptSkip_injective` in one argument. There is no same-branch
premise, no prior prefix-preservation premise, and no new assumption on
the total map. All old E atoms, absent directed L-atoms and singleton
facts are recovered, including those at the distinguished coordinate.

The recovery operation is raw-valued. Do not infer that deleting an
arbitrary ordinary coordinate from an arbitrary admissible type preserves
admissibility. Its admissibility on the candidate's image follows because
it returns the original admissible node.

See the new recovery/injectivity checkpoint for exact verification status;
this checklist is not a substitute for its proof evidence.

## Agreement with the prescribed partial function -- OPEN

For S in source at level ell, compatibility with itself forces the
matching branch. Compare its complete inserted record with F.target S.
B1 handles old coordinates, B2 supplies the complete ordinary output
socle, and the selected upper column supplies the two L-relations to the
distinguished vertex. The E comparison is a distinct obligation; an
L-reduct equality alone is insufficient. The target's admissibility
provides its last-E atom and its valid ordinary E cut. Do not assume the
output equality in the image relation.

## All predecessors and order embedding -- GREEN

The common implementation is `PrescribedKptPrefixCases.lean`,
`PrescribedKptPrefixMatching.lean`, and `PrescribedKptFullPrefix.lean`.
It derives the common compatibility decision on upper source chains;
computes matching images with the same source and inserted cut using the
actual one-filler prefix replica; reuses the neutral upper-prefix theorem;
and checks all crossing-gap atoms directly. The full endpoint is
`PrescribedBoringData.prescribedKptSkip_prefix`. No extra age, same-branch,
representation, or abstract monotonicity premise is added.

`PrescribedKptOrderEmbedding.lean` derives the exact admissible ancestor
identity at every n <= level(a), with image cut n below ell and n+1 at or
above ell. It also derives order reflection and packages the actual map
as `prescribedKptOrderEmbedding`. Order reflection takes an admissible
prefix of the longer source at the shorter source's level, compares the
equal-level image prefixes, and applies the established injectivity.
There is no assumption that arbitrary coordinate deletion is admissible.

The overlapping implementation in PR216 is archived as an alternative,
not imported alongside the common implementation. The active checkpoint
records exact tested heads and audit evidence; it is not a ShapeMap claim.

## Weak successors below and across the gap -- GREEN

`PrescribedKptGapSucc.lean` first combines matching and neutral self-prefix
facts at level ell. For a successor base below ell, the actual S-tree
parameter-level axiom puts every parameter still lower; both base and
parameter list are fixed. The old successor is then the required witness
below the mapped child. It is fixed strictly below ell and is a genuine
prefix of its image at level ell. No equality with the mapped child is
asserted at the crossing edge ell-1 -> ell.

## Successors based at or above the gap -- OPEN

Transport the canonical empty-or-singleton parameter list and the exact
terminal Sigma letter using this same concrete node map. Use the exact
finite-constructor representation for all old ordinary coordinates,
including vertices whose free level lies below ell and therefore do not
choose the upper branch. Then invoke canonical decomposition uniqueness.
The lower/crossing weak law and the order embedding do not supply these
identities. Parallel PR220 stages a finite terminal-letter result, but it
is not imported into this active stack yet.

## Obligations outside this map construction

M2 still needs a necessity or replacement decomposition argument deriving
the corrected common-socle L-age B3 condition. The older third clause
of lem:comp is not a proved source of the strengthened test.
M3 still needs the repaired B3 age test for its actual duplication
prescription. I3/signature witnesses must be finite L-structures, not
subject to the rejected E-partial-structure premises. Neither the full
boring extension lemma nor the final big-Ramsey bound is certified by
the order embedding and predecessor identities of the present map.
