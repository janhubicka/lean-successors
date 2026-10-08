import SuccessorTree.V10.Counting
import SuccessorTree.V10.MeetTrace
import SuccessorTree.V10.BlockOrder

-- The three estimates below are conditional: they do not silently assume the
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
