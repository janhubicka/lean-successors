import SuccessorTree.V10.LevelRemovalUniformParameter
import SuccessorTree.V10.LevelRemovalCanonicalStepAssembly
import SuccessorTree.V10.LevelRemovalDeletedWeakTarget
import SuccessorTree.V10.LevelRemovalUniformLowWeakSucc
import SuccessorTree.V10.LevelRemovalHighStepSafety

/-! Four composable checked-form candidate components of the normalized
M2 deletion proof, tested together without an abstract M2 axiom.
These endpoints by themselves do NOT prove the upper weak successor
condition, the global ShapeMap, or corrected finite L-only B3. -/
#print axioms SuccessorTree.V10.uniformGapDeletedKpt_raw_if_above
#print axioms SuccessorTree.V10.uniformGapDeletedKpt_raw_parameter_list
#print axioms SuccessorTree.V10.canonicalKptStep_of_deleted_record
#print axioms SuccessorTree.V10.admissible_deleted_raw_predecessor
#print axioms SuccessorTree.V10.deleted_predecessor_node_of_admissible_upper
#print axioms SuccessorTree.V10.uniformGapDeletedKpt_low_parameter_list
#print axioms SuccessorTree.V10.uniformGapDeletedKpt_crossing_weak_succ
#print axioms SuccessorTree.V10.uniformGapDeletedKpt_low_weak_succ

-- The sharp guard is derived from the real mapped canonical step.
#print axioms SuccessorTree.V10.mapped_upper_canonical_step_safe_for_gap
