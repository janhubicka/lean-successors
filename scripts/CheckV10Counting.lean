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
import SuccessorTree.V10.HRelations
import SuccessorTree.V10.OriginalPoolEnvelope
import SuccessorTree.V10.CanonicalParameters
import SuccessorTree.V10.CanonicalObservation
import SuccessorTree.V10.HAge
import SuccessorTree.V10.HGenerationRank
import SuccessorTree.V10.HRelocation
import SuccessorTree.V10.RelocationCopy
import SuccessorTree.V10.RelocationIrreducible
import SuccessorTree.V10.RelocationOrder
import SuccessorTree.V10.FiniteMeetBudget
import SuccessorTree.V10.HAgeProjection
import SuccessorTree.V10.SignatureSplice

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
#print axioms SuccessorTree.V10.representedClosure_or_root
#print axioms SuccessorTree.V10.generated_positive_meet_has_originals
#print axioms SuccessorTree.V10.copiedRealPair_eq_of_admissible
#print axioms SuccessorTree.V10.copiedRealPair_empty_of_not_admissible
#print axioms SuccessorTree.V10.copiedRealPair_nonempty_implies_admissible
#print axioms SuccessorTree.V10.nonemptyCopiedPair_generatesE
#print axioms SuccessorTree.V10.sameBlock_no_binary
#print axioms SuccessorTree.V10.copiedRealPair_matches_trace
#print axioms SuccessorTree.V10.prefixesOf_meetClosed
#print axioms SuccessorTree.V10.closure_subset_original_pool
#print axioms SuccessorTree.V10.closure_meet_has_originals
#print axioms SuccessorTree.V10.canonicalRule_parameterClosed
#print axioms SuccessorTree.V10.closure_subset_pool_of_canonicalRule
#print axioms SuccessorTree.V10.closure_positiveMeet_of_canonicalRule
#print axioms SuccessorTree.V10.canonicalRule_of_decomposition
#print axioms SuccessorTree.V10.closure_subset_pool_of_decomposition
#print axioms SuccessorTree.V10.parameterClosed_iff_canonicalPrincipal
#print axioms SuccessorTree.V10.parameterClosed_iff_canonicalPrincipalOn
#print axioms SuccessorTree.V10.HCrossAllowed_swap
#print axioms SuccessorTree.V10.HBinary_fake_left
#print axioms SuccessorTree.V10.HBinary_same_first
#print axioms SuccessorTree.V10.HLinked_real
#print axioms SuccessorTree.V10.HLinked_gate
#print axioms SuccessorTree.V10.HBinary_eq_base_of_link
#print axioms SuccessorTree.V10.irreducible_pair_projects_to_base
#print axioms SuccessorTree.V10.HBinary_top_copy
#print axioms SuccessorTree.V10.HUnary_top_copy
#print axioms SuccessorTree.V10.HDiagonal_top_copy
#print axioms SuccessorTree.V10.hPosition_top_order
#print axioms SuccessorTree.V10.linked_increasing_generation
#print axioms SuccessorTree.V10.generation_rank_lower_bound
#print axioms SuccessorTree.V10.ordered_linked_generation_rank
#print axioms SuccessorTree.V10.relocated_lower_pairs
#print axioms SuccessorTree.V10.relocated_lower_upper_pair
#print axioms SuccessorTree.V10.relocated_singleton_data
#print axioms SuccessorTree.V10.mixedBinary_eq_after_lower_relocation
#print axioms SuccessorTree.V10.mixedUnary_eq_after_lower_relocation
#print axioms SuccessorTree.V10.mixedDiagonal_eq_after_lower_relocation
#print axioms SuccessorTree.V10.linked_firstIndex_lt_of_position_lt
#print axioms SuccessorTree.V10.irreducible_mixedBinary_eq_after_relocation
#print axioms SuccessorTree.V10.relocated_lower_order
#print axioms SuccessorTree.V10.relocated_lower_before_upper
#print axioms SuccessorTree.V10.relocated_lower_avoids_old_last
#print axioms SuccessorTree.V10.poolMeetLevelBudget_card_le
#print axioms SuccessorTree.V10.original_level_mem_budget
#print axioms SuccessorTree.V10.original_pair_meet_level_mem_budget
#print axioms SuccessorTree.V10.closure_nontrivial_meet_level_mem_budget
#print axioms SuccessorTree.V10.selectedLevels_card_le_quadratic
#print axioms SuccessorTree.V10.every_irreducible_H_vertex_is_real
#print axioms SuccessorTree.V10.irreducible_H_copy_projects_to_base
#print axioms SuccessorTree.V10.ordered_irreducible_H_copy_projects_to_base

-- Exact conditional ordered splicing of two matching age-change signatures.
-- These check the complete atom-preserving construction, not the KFpt adapter.
#print axioms SuccessorTree.V10.signatureSplice_order_avoids
#print axioms SuccessorTree.V10.signatureSplice_binary
#print axioms SuccessorTree.V10.signatureSplice_singleton
#print axioms SuccessorTree.V10.signatureSplice_inducedCopy
