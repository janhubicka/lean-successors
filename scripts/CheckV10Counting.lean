import SuccessorTree.V10.Counting
import SuccessorTree.V10.MeetTrace
import SuccessorTree.V10.BlockOrder
import SuccessorTree.V10.MeetBundle
import SuccessorTree.V10.FirstDisagreement
import SuccessorTree.V10.MeetProvenance
import SuccessorTree.V10.SocleBound
import SuccessorTree.V10.AncestorMeet
import SuccessorTree.V10.SocleE
import SuccessorTree.V10.RecordBridge
import SuccessorTree.V10.OriginalPool

-- The estimates below are conditional: they do not silently assume the
-- H-structure meet formula or the missing uniqueness of age signatures.
set_option autoImplicit false

#print axioms SuccessorTree.V10.meetLevels_card_le
#print axioms SuccessorTree.V10.ageLevels_card_le_pow
#print axioms SuccessorTree.V10.ageLevels_card_le_family
#print axioms SuccessorTree.V10.nonemptySupports_card
#print axioms SuccessorTree.V10.newlySelected_card_le

#print axioms SuccessorTree.V10.traceBit_before_smaller
#print axioms SuccessorTree.V10.traceBit_first_positive_difference
#print axioms SuccessorTree.V10.traceBit_equal_generation_zero
#print axioms SuccessorTree.V10.traceBit_small_at_own
#print axioms SuccessorTree.V10.positiveMismatch_firstNeighbour
#print axioms SuccessorTree.V10.firstPositiveDisagreement_block
#print axioms SuccessorTree.V10.hPosition_lt_of_block_lt
#print axioms SuccessorTree.V10.hPosition_lt_of_gen_lt
#print axioms SuccessorTree.V10.hPosition_before
#print axioms SuccessorTree.V10.firstPositiveDisagreement_realPositions
#print axioms SuccessorTree.V10.bundledPositiveMismatch_firstNeighbour
#print axioms SuccessorTree.V10.bundledTrace_empty_of_zero
#print axioms SuccessorTree.V10.positiveDisagreement_commonPair
#print axioms SuccessorTree.V10.firstPositiveDisagreement_classifies
#print axioms SuccessorTree.V10.meet_eq_of_nontrivial_prefixes
#print axioms SuccessorTree.V10.meet_mem_prefixesOf
#print axioms SuccessorTree.V10.nontrivial_meet_has_originals
#print axioms SuccessorTree.V10.positivePosition_below_free_iff
#print axioms SuccessorTree.V10.positiveMeet_lowerBlock_guard
#print axioms SuccessorTree.V10.meet_eq_of_adjacent_ancestors
#print axioms SuccessorTree.V10.meet_level_of_adjacent_ancestors
#print axioms SuccessorTree.V10.generatedE_nonTop_iff
#print axioms SuccessorTree.V10.generatedE_top_iff
#print axioms SuccessorTree.V10.generatedE_empty_of_initial
#print axioms SuccessorTree.V10.generatedE_nonTop_firstMissing
#print axioms SuccessorTree.V10.generatedE_top_firstMissing
#print axioms SuccessorTree.V10.oddFake_not_E_isolated
#print axioms SuccessorTree.V10.generatedE_downward
#print axioms SuccessorTree.V10.generatedE_gap
#print axioms SuccessorTree.V10.generatedE_of_allowedPair
#print axioms SuccessorTree.V10.meet_of_first_record_difference
#print axioms SuccessorTree.V10.meet_level_of_first_record_difference
#print axioms SuccessorTree.V10.representedClosure_subset_prefixesOf
#print axioms SuccessorTree.V10.generated_nontrivial_meet_has_originals
