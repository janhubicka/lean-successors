# Prescribed one-gap map: verified endpoints and remaining applications

The concrete prescribed ShapeMap and the boring-extension conclusion are
verified in the normalized finite Boolean L+ representation by the focused
V10 build and named transitive axiom audits at PRs #226 and #227.
The original-language adapter and uses in M2/M3 remain independent.

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

## Agreement with f -- GREEN

`PrescribedSourceValues.lean` reconstructs the entire L-reduct of the
literal inserted source. `PrescribedSourceE.lean` independently checks
the auxiliary E record; `PrescribedSourceFullValue.lean` combines them
into exact equality with f(S) for every admissible prescribed source.
`prescribedKptSkip_agrees_on_source` compares the selected global image,
not an arbitrary finite image relation. The endpoint was checked in
PR #218 without an additional compatibility or E-age assumption.

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

## Successors based at or above the gap -- GREEN

`PrescribedTerminalLetter.lean` preserves the full terminal Sigma letter,
including old E pairs, for the literal prescribed insertion.
`PrescribedOldParameter.lean` proves exact selected old-vertex images
at every free cut and transports the canonical empty-or-singleton list.
Both components passed full Lean and focused audits in PRs #223/#224.

`PrescribedUpperSuccMatching.lean` and
`PrescribedUpperSuccUnmatched.lean` now establish the exact above-gap
canonical successor law in the prescribed and neutral branches,
respectively. `PrescribedKptShapeMap.lean` combines this law with the
independently verified weak below/crossing case and constructs the
concrete ShapeMap. PR #226's focused V10 build and axiom audit passed.

## Exact skipped level and complete boring extension -- GREEN

`PrescribedBoringCompletion.lean` obtains `SkipsOnly ell` from
`admissibleKptLevel_nonempty` and the checked level shift. Its endpoint
`prescribedKpt_boring_extension_exists` packages the ShapeMap in KptM
with the omitted level and complete agreement with f. PR #227's
focused V10 build and axiom audit passed. PR #228 separately imports
this public endpoint from `SuccessorTree.lean` so the default full
Lean library build checks it as well.

## Obligations outside this map construction

M2 still needs a necessity or replacement decomposition argument deriving
the corrected common-socle L-age B3 condition. The older third clause
of lem:comp is not a proved source of the strengthened test.
M3 still needs the repaired B3 age test for its actual duplication
prescription. I3/signature witnesses must be finite L-structures, not
subject to the rejected E-partial-structure premises. The normalized finite-language boring extension lemma is certified.
The final big-Ramsey bound is not certified by this lemma alone.
