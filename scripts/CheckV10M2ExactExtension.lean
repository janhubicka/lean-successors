import SuccessorTree.V10.LevelRemovalM2ExactExtension

-- Every proof is independent of the SMTree M2 field and relies on
-- standard Lean axioms only; no new insertion/existence axiom is added.
#print axioms SuccessorTree.SMTree.strictMono_nat_range_compl_singleton
#print axioms SuccessorTree.SMTree.eq_id_below_of_level_eq
#print axioms SuccessorTree.V10.kptShapeLevelMap_eq
#print axioms SuccessorTree.V10.kptShapeLevelMap_strictMono
#print axioms SuccessorTree.V10.kptShapeLevelMap_range
#print axioms SuccessorTree.V10.kptShapeMap_skipsOnly_level
#print axioms SuccessorTree.V10.kptShapeMap_fixed_below_skip
#print axioms SuccessorTree.V10.uniformGapDeletedShapeMap_boundary_extension_iff
#print axioms SuccessorTree.V10.uniformGapDeletedShapeMap_factorization_of_boundary_extension
