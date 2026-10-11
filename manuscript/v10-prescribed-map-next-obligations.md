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

## All predecessors -- OPEN

For b <= a with both levels at least ell, use the actual one-filler
`prefixReplicaPartialStructure` already used in
`LocalAgeNeutralPrefix.lean`. First derive that restricting a and b to
ell gives the same complete record. Consequently they make the same
compatibility decision; this is not a premise to add.

In the matching case, represent a by A,v and put d = level(b). The replica
R = prefixReplicaPartialStructure A v d realizes b at distinguished
address d+1. Derive the same compatible prescribed source S0 for both.
Choose its valid inserted cut once. The new
`matchingKptImage_raw_eq_of_representation` computes b's selected image
in R with that same cut. `matching_constructor_avoids_of_valid_cut`
derives the needed avoidance from corrected B3, not from a new hypothesis
about the replica insertion. Use the full prescribed record-independence
theorem at cut d to compare this inserted replica with the restriction
of the insertion of A; it permits their different distinguished indices.
Finish with `rawPartialType_prefix_of_cut` and the exact free-level laws.

In the unmatched case, reuse the neutral prefix theorem. For prefixes
below the gap, extract only retained old coordinates. Use
`record_eq_of_rawTypeAtFree` to avoid repeating dependent Sigma casts.
The arbitrary-representation adapter is not itself the prefix theorem.

## Successors -- OPEN

Above the gap, transport the canonical empty-or-singleton parameter
list and the exact terminal Sigma letter, using the same concrete node
map. At the edge ell-1 -> ell the parent and parameters below ell are
fixed. The ordinary successor at level ell need only be a prefix of the
mapped child at level ell+1. Prove that weak statement separately; exact
equality with the mapped child is not the required boundary law.

## Obligations outside this map construction

M2 still needs a necessity or replacement decomposition argument deriving
the corrected common-socle L-age B3 condition. The older third clause
of lem:comp is not a proved source of the strengthened test.
M3 still needs the repaired B3 age test for its actual duplication
prescription. I3/signature witnesses must be finite L-structures, not
subject to the rejected E-partial-structure premises. Neither the full
boring extension lemma nor the final big-Ramsey bound is certified by
totality and injectivity of the present candidate map.
