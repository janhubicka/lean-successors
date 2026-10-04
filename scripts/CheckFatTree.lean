import SuccessorTree.FatTree.Reduction

open SuccessorTree

#check SMTree.FatTree
#check SMTree.FiniteFatTree
#check SMTree.FiniteFatTree.terminalCut
#check SMTree.FatTree.initialSegment_terminalCut
#check SMTree.FiniteFatTree.rowExtension
#check SMTree.FiniteFatTree.rowExtension_level_succ
#check SMTree.FiniteFatTree.rowExtension_fixesBelow
#check SMTree.FiniteFatTree.oneLift
#check SMTree.FiniteFatTree.oneLift_subset_nextLevel
#check SMTree.FiniteFatTree.oneLift_mem_of_mem_full_of_source
#check SMTree.FatTree.cut_strictMono
#check SMTree.FatTree.rowExtension_level_succ
#check SMTree.MMap.le_apply_of_fixesBelow
#check SMTree.FatTree.rowExtension_fixesBelow
#check SMTree.FatTree.oneLift_subset_nextLevel
#check SMTree.FatTree.oneLift_descends
#check SMTree.FatTree.oneLift_mem_of_mem_full_of_source
#check SMTree.FatTree.liftSteps_subset_level
#check SMTree.FatTree.liftSteps_add
#check SMTree.FatTree.liftSteps_descends
#check SMTree.FatTree.liftSteps_mem_of_mem_of_source
#check SMTree.FatTree.liftTo_subset_level
#check SMTree.FatTree.liftTo_split
#check SMTree.FatTree.liftTo_descends
#check SMTree.FatTree.liftTo_mem_of_mem_of_source

#print axioms SMTree.FatTree.cut_strictMono
#print axioms SMTree.FatTree.rowExtension_level_succ
#print axioms SMTree.MMap.le_apply_of_fixesBelow
#print axioms SMTree.FatTree.oneLift_mem_of_mem_full_of_source
#print axioms SMTree.FatTree.liftSteps_mem_of_mem_of_source

#check SMTree.FatTree.ReductionWitness
#check SMTree.FatTree.ReductionWitness.index_zero
#check SMTree.FatTree.ReductionWitness.liftSteps_subset_liftTo
#check SMTree.FatTree.ReductionWitness.liftTo_subset_liftTo
#check SMTree.FatTree.ReductionWitness.trans
#check SMTree.FatTree.reduces_refl
#check SMTree.FatTree.reduces_trans
#print axioms SMTree.FatTree.ReductionWitness.index_zero

#print axioms SMTree.FatTree.ReductionWitness.trans
#print axioms SMTree.FatTree.reduces_trans
