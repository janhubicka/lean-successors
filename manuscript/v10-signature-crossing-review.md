# Actual Kpt crossing to signature full type (PR 165)

Checkpoint: `b44d378e7d19d937669c90bad3e20f407ee540ff`.
Focused V10 build and transitive axiom audit run `38056182806` passed.
The full repository run is tracked separately in the PR.

## What is now proved

`admissibleKpt_original_ancestor_value` identifies the actual
`LevelTree.ancestor` of a type represented by an ambient original with the
complete induced L+ prefix extracted from that ambient partial structure.

`actualKpt_crossing_implies_fullAtomic` then shows that an upper vertex
realizing the L-reduct of the named genuine crossing has exactly the complete
directed atomic L-type of its ambient original through the tested cut. This
includes unary, diagonal, both binary orientations, and negative binary facts.

`signature_collision_impossible_of_actual_kpt_crossings` feeds these
derived full types into the previously checked ambient signature splice. Thus
two equal positive-level signatures cannot occur once their age-test witnesses
are known to realize the prescribed actual crossings.

## Boundary

This does not manufacture the age-test witness. Lemma 6.51 still has to
construct the global one-level insertion/shape map and prove its finite
forbidden-free age from the three-clause age condition. PR 166 starts that
formalization. Therefore the crossing-to-full-type and collision part is
GREEN, while the application to actual I3 levels remains conditional on the
local-age construction.

The language normalization/exact-H wording and global M2/M3 tasks remain
separate. No independent referee agents were invoked in this checkpoint.
