import SuccessorTree.V10.LevelRemovalUniformParameter
import SuccessorTree.V10.LevelRemovalCanonicalStepAssembly
import SuccessorTree.V10.LevelRemovalDeletedWeakTarget
import SuccessorTree.V10.LevelRemovalUniformLowWeakSucc
import SuccessorTree.V10.LevelRemovalHighStepSafety

/-!
Joint integration gate: after the verified #309 safety branch, the
intrinsic parameter action, admissible deleted target, reconstructed
canonical successor and low/crossing weak successor coexist in one
compilation universe. The next all-level weak successor may be added
without assuming M2 or importing an ad hoc age lemma.
-/

#print axioms SuccessorTree.V10.uniformGapDeletedKpt_raw_parameter_list
#print axioms SuccessorTree.V10.canonicalKptStep_of_deleted_record
#print axioms SuccessorTree.V10.deleted_predecessor_node_of_admissible_upper
#print axioms SuccessorTree.V10.uniformGapDeletedKpt_low_weak_succ
#print axioms SuccessorTree.V10.mapped_upper_canonical_step_safe_for_gap
