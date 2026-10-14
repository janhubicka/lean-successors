import SuccessorTree.V10.M3LiteralDuplication
import SuccessorTree.V10.M3RepresentativeIndependence
import SuccessorTree.V10.LevelRemovalType

/-!
Exact cross-stack source audit for the verified normalized M3 law and
the distinct local M2 deletion/type-transport theorem. Running both
together prevents independent PR integration from hiding a dependency.
This does not assert the global M2 factorization or language adapter.
-/

#print axioms SuccessorTree.V10.m3OneGapShapeMap_literalM3
#print axioms SuccessorTree.V10.m3FiniteTarget_eq_of_representation
#print axioms SuccessorTree.V10.deleteAtPartial_partialTypeAt_eq_deleteOrdinary
