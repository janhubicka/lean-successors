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
import SuccessorTree.V10.SignatureProfiles
import SuccessorTree.V10.SignatureTypePrefix
import SuccessorTree.V10.SignatureCollision
import SuccessorTree.V10.AmbientSignature
import SuccessorTree.V10.RelationalTypeReduct
import SuccessorTree.V10.EFreeLevel
import SuccessorTree.V10.PartialStructureE
import SuccessorTree.V10.HExactE
import SuccessorTree.V10.PartialTypeRestriction
import SuccessorTree.V10.HELinkage
import SuccessorTree.V10.CommonSocleType
import SuccessorTree.V10.FirstFullPrefix
import SuccessorTree.V10.RawTypeMeet
import SuccessorTree.V10.RawMeetLevel
import SuccessorTree.V10.RawPrefixOrder
import SuccessorTree.V10.PrefixReplicaE
import SuccessorTree.V10.PrefixReplicaL
import SuccessorTree.V10.PrefixReplicaPartial
import SuccessorTree.V10.PrefixReplicaAge

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

#print axioms SuccessorTree.V10.signatureSplice_in_laterDomain
#print axioms SuccessorTree.V10.signatureSplice_cross_of_sharedProfiles

#print axioms SuccessorTree.V10.fullAtomicTypePrefix_cross
#print axioms SuccessorTree.V10.signatureSplice_cross_of_fullTypePrefixes

#print axioms SuccessorTree.V10.signature_collision_impossible_of_common_full_types

-- Restrict complete types from one ambient original at two age-test cuts.
#print axioms SuccessorTree.V10.fullAtomicTypePrefix_restrict
#print axioms SuccessorTree.V10.common_original_gives_equal_short_types
#print axioms SuccessorTree.V10.signature_collision_impossible_of_ambient_types

-- Extract the literal induced L-reduct of a partial type, separately from E.
#print axioms SuccessorTree.V10.RelationalPrefixType.ofAgeModel_toAtomic
#print axioms SuccessorTree.V10.equal_reduct_types_imply_fullAtomic
#print axioms SuccessorTree.V10.prescribed_crossing_implies_fullAtomic
#print axioms SuccessorTree.V10.PartialTypeWithE.eq_implies_lReduct

-- Unique first E gap follows from spacing and downward closure, not an axiom.
#print axioms SuccessorTree.V10.e_iff_lt_freeCut
#print axioms SuccessorTree.V10.freeCut_unique
#print axioms SuccessorTree.V10.exists_freeCut
#print axioms SuccessorTree.V10.existsUnique_freeCut
#print axioms SuccessorTree.V10.canonicalFreeLevel_isFreeCut
#print axioms SuccessorTree.V10.canonicalFreeLevel_le
#print axioms SuccessorTree.V10.e_iff_lt_canonicalFreeLevel

-- Literal E-socle extraction from Definition 6.28: not an extra axiom.
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.E_iff_freeLevel
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.freeLevel_le
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.partialTypeAt_lReduct
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.partialTypeAt_fullESocle
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.partialTypeAt_no_reverseE
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.partialTypeAt_no_typeE_loop
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.freeLevel_firstMissing

-- Exact global H-E formula: all source coordinates, fake vertices included.
#print axioms SuccessorTree.V10.hPosition_injective_bounded
#print axioms SuccessorTree.V10.exactHEBool_true_iff
#print axioms SuccessorTree.V10.exactHEBool_at_real_iff
#print axioms SuccessorTree.V10.exactHEBool_spaced
#print axioms SuccessorTree.V10.exactHEBool_downward
#print axioms SuccessorTree.V10.exactHEBool_freeLevel_eq_of_column
#print axioms SuccessorTree.V10.exactHEBool_nonTop_freeLevel
#print axioms SuccessorTree.V10.exactHEBool_top_freeLevel
#print axioms SuccessorTree.V10.exactHEBool_initial_freeLevel

-- Fake vertices have empty incoming E but may belong to later E-socles.
#print axioms SuccessorTree.V10.hPosition_even
#print axioms SuccessorTree.V10.exactHEBool_odd_target_false
#print axioms SuccessorTree.V10.exactHEBool_fake_freeLevel
#print axioms SuccessorTree.V10.exactHEBool_odd_source_not_isolated

-- Every L+ record component commutes with initial-socle restriction.
#print axioms SuccessorTree.V10.prefixVertexIndex_lift
#print axioms SuccessorTree.V10.RelationalPrefixType.eq_of_atoms
#print axioms SuccessorTree.V10.RelationalPrefixType.ofAgeModel_restrict
#print axioms SuccessorTree.V10.PartialTypeWithE.eq_of_atoms
#print axioms SuccessorTree.V10.EnumeratedPartialStructure.partialTypeAt_restrict

-- Definition 6.28(3) for the complete exact H model, no new axioms.
#print axioms SuccessorTree.V10.exactHEBool_of_linked_real_positions
#print axioms SuccessorTree.V10.exactHEBool_of_HLinked_increasing
#print axioms SuccessorTree.V10.exactH_satisfies_E_axioms

-- First complete L+ record mismatch equals first binary crossing mismatch
-- under the same ambient socle, equal singleton roots and positive free cuts.
#print axioms SuccessorTree.V10.sameAmbient_partialType_eq_of_cross
#print axioms SuccessorTree.V10.sameAmbient_cross_of_partialType_eq
#print axioms SuccessorTree.V10.sameAmbient_partialType_eq_iff_cross
#print axioms SuccessorTree.V10.sameAmbient_first_fullType_difference

-- Actual longest common induced L+ prefixes, including E and both binary orientations.
#print axioms SuccessorTree.V10.fullPartialType_eq_at_smaller
#print axioms SuccessorTree.V10.exists_maximal_common_fullPrefix
#print axioms SuccessorTree.V10.maximal_common_fullPrefix_unique
#print axioms SuccessorTree.V10.binary_witness_of_first_fullPrefix_difference
#print axioms SuccessorTree.V10.exists_maximal_common_fullPrefix_with_binary_witness

-- Universal property of actual complete L+ prefixes from a common ambient.
#print axioms SuccessorTree.V10.rawPartialType_prefix_of_cut
#print axioms SuccessorTree.V10.rawPartialTypes_have_greatest_common_prefix

-- A genuine first binary difference fixes the universal raw L+ meet level.
#print axioms SuccessorTree.V10.rawPartialType_meet_level_of_first_binary_difference

-- Exact raw L+ prefix-order laws, unique ancestors, and forest geometry.
#print axioms SuccessorTree.V10.PartialTypeWithE.restrict_self
#print axioms SuccessorTree.V10.PartialTypeWithE.restrict_trans
#print axioms SuccessorTree.V10.rawPartialTypePrefix_refl
#print axioms SuccessorTree.V10.rawPartialTypePrefix_trans
#print axioms SuccessorTree.V10.rawPartialTypePrefix_antisymm
#print axioms SuccessorTree.V10.rawPartialTypePrefix_level_le
#print axioms SuccessorTree.V10.rawPartialTypePrefix_eq_of_same_level
#print axioms SuccessorTree.V10.rawPartialTypeAncestor_le
#print axioms SuccessorTree.V10.rawPartialType_lower_linear
#print axioms SuccessorTree.V10.rawPartialType_ancestor_exists

-- One neutral filler suffices to realize any shorter E-socle with exact free cut.
#print axioms SuccessorTree.V10.prefixReplicaE_old
#print axioms SuccessorTree.V10.prefixReplicaE_last_iff
#print axioms SuccessorTree.V10.prefixReplicaE_spaced
#print axioms SuccessorTree.V10.prefixReplicaE_downward
#print axioms SuccessorTree.V10.prefixReplicaE_last_freeCut
#print axioms SuccessorTree.V10.prefixReplicaE_last_freeLevel
#print axioms SuccessorTree.V10.prefixReplicaE_preserves_type_socle
#print axioms SuccessorTree.V10.prefixReplicaE_preserves_old_socle

-- Full induced directed L-reduct of the one-filler prefix replica.
#print axioms SuccessorTree.V10.prefixReplicaAddress_old
#print axioms SuccessorTree.V10.prefixReplicaAddress_last
#print axioms SuccessorTree.V10.prefixReplicaAddress_filler
#print axioms SuccessorTree.V10.prefixReplicaL_old
#print axioms SuccessorTree.V10.prefixReplicaL_last_singleton
#print axioms SuccessorTree.V10.prefixReplicaL_cross
#print axioms SuccessorTree.V10.prefixReplicaL_filler_neutral
#print axioms SuccessorTree.V10.prefixReplicaL_type_eq

-- Actual one-filler partial structure satisfies E1-E3 and realizes shortened type.
#print axioms SuccessorTree.V10.prefixReplicaPartialStructure_freeLevel
#print axioms SuccessorTree.V10.prefixReplicaPartialStructure_type_eq

-- Ordered induced forbidden-copy preservation under one-filler replica.
#print axioms SuccessorTree.V10.prefixReplicaProject_address
#print axioms SuccessorTree.V10.prefixReplicaProject_strictMono_on
#print axioms SuccessorTree.V10.irreducible_replica_copy_avoids_filler
#print axioms SuccessorTree.V10.replica_copy_projects_to_original
#print axioms SuccessorTree.V10.prefixReplicaL_preserves_avoidance_nontrivial

-- Singleton case: the isolated filler has the allowed neutral type.
#print axioms SuccessorTree.V10.nonNeutral_singleton_replica_copy_avoids_filler
#print axioms SuccessorTree.V10.prefixReplicaL_preserves_avoidance_singleton
