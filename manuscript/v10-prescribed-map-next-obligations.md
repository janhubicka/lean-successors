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

## Agreement with the prescribed partial function

For S in source at level ell, compatibility with itself forces the
matching branch. Compare its complete inserted record with F.target S.
B1 handles old coordinates, B2 supplies the complete ordinary output
socle, and the selected upper column supplies the two L-relations to the
distinguished vertex. The E comparison is a distinct obligation; an
L-reduct equality alone is insufficient. The target's admissibility
provides its last-E atom and its valid ordinary E cut. Do not assume the
output equality in the image relation.

## All predecessors

For two upper comparable nodes, use the actual one-filler
`prefixReplicaPartialStructure` already used in
`LocalAgeNeutralPrefix.lean`. A shared ell-prefix means they make the same
compatibility decision. In the matching case, apply the full prescribed
record-independence theorem at the shorter cut to the original ambient
model and its prefix replica, permitting their different distinguished
vertex indices. In the unmatched case, reuse the neutral prefix theorem.
For prefixes below the gap, extract only retained old coordinates.
Use `record_eq_of_rawTypeAtFree` to avoid repeating dependent Sigma casts.

## Node injectivity, including mixed branches

The strict numerical level formula first forces equal source levels.
For upper nodes, reflect equality of the inserted complete records by
restricting to the shifted old coordinates. This needs one old-atom
recovery statement valid for prescribed/prescribed, neutral/neutral,
and prescribed/neutral comparisons. Do not prove only the first two
cases: nodes with different ordinary socles may choose different
branches. All old E atoms and absent directed L-atoms must be recovered.
Below the gap, nodes are fixed.

## Successors

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
the present total-map result.
