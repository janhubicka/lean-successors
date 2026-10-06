import SuccessorTree.FatTree.A4ReviewGoodPair
import SuccessorTree.FatTree.A4ReviewSourceFusion
import SuccessorTree.FatTree.A4ReviewComplete

open SuccessorTree.SMTree.FatTree

#check persistentAcceptedPair_of_dense_pairs
#check ProfileReplayState.review_common_tail_replays
#check ProfileReplayState.review_raw_fan_represented
#check ProfileReplayState.review_exists_profile_fan_homogeneity
#check exists_lastBlock_exactTrace_of_successors
#check exists_lastBlock_exactTrace_of_sourceLetter
#check review_goodPair_of_sourceLetter
#check review_trace_persistence_core
#check review_all_trace_fusion_of_persistence
#check review_trace_persistence_of_sourceLetter
#check review_all_trace_fusion_of_sourceLetter
#check review_fixedStemPigeonhole_of_sourceLetter
#check review_fixedStemPigeonhole
#check fixedStemPigeonhole_review
#check abstractRamseySpace_review
#check ellentuck_review
#check fatTreeFixedStemPigeonhole
#check fatTreeA4
#check fatTreeAbstractRamseySpace
#check fatTreeEllentuck
#print axioms oneBlockOccurs_of_reduces
#print axioms oneBlockOccurs_of_pair
#print axioms appendRow_injective
#print axioms headsAtDepth_finite
#print axioms eliminate_accepted_pair_at_depth
#print axioms eliminate_accepted_pair_batch
#print axioms eliminate_all_accepted_pairs_at_depth
#print axioms persistentAcceptedPair_of_dense_pairs
#print axioms review_goodRows_transport
#print axioms review_good_row_of_good_prefix
#print axioms review_rowExtension_succ
#print axioms ProfileReplayState.review_common_const_letter
#print axioms ProfileReplayState.review_first_parameter_edge
#print axioms ProfileReplayState.review_common_letter_agrees
#print axioms ProfileReplayState.reviewTailEval_replay
#print axioms ProfileReplayState.reviewTailEval_eq_foldl_state
#print axioms ProfileReplayState.review_common_tail_replays
#print axioms review_letter_for_admissible_successors
#print axioms ProfileReplayState.review_seen_of_admissible_successors
#print axioms ProfileReplayState.review_head_raw_fan_edge
#print axioms ProfileReplayState.review_raw_fan_represented
#print axioms review_AM_ext_top
#print axioms ProfileReplayState.review_word_eval
#print axioms ProfileReplayState.review_lineTail_composite
#print axioms ProfileReplayState.review_exists_profile_fan_homogeneity
#print axioms ReviewFanLine.depths_strict
#print axioms exists_reviewFanLine_of_sourceLetter
#print axioms review_AM_level
#print axioms review_composeAcross_end
#print axioms review_composeAcross_canonical
#print axioms reviewTransportFan
#print axioms reviewTransportFan_apply
#print axioms reviewExactComp
#print axioms review_composeAcross_assoc
#print axioms review_exists_fan_of_pointwise
#print axioms reviewFanLine_factor_colour
#print axioms review_occurs_after_matching_stem
#print axioms review_realize_head
#print axioms review_trace_transport
#print axioms review_trace_prefix_transport
#print axioms review_composeAcross_heq
#print axioms reviewBridgeMap
#print axioms reviewBridgeMap_heq
#print axioms reviewCastExactSource
#print axioms review_composeAcross_cast_source
#print axioms exists_lastBlock_exactTrace_of_successors
#print axioms exists_lastBlock_exactTrace_of_sourceLetter
#print axioms review_bridges_nonempty_of_sourceLetter
#print axioms review_persistent_line_witness_of_sourceLetter
#print axioms review_goodPair_finite_family_of_sourceLetter
#print axioms review_goodPair_at_prefix_of_sourceLetter
#print axioms review_goodPair_of_sourceLetter
#print axioms oneBlock_mem_of_all_fixedTraceGoodRows_of_successors
#print axioms oneBlock_mem_of_all_fixedTraceGoodRows_of_sourceLetter
#print axioms review_trace_persistence_core
#print axioms review_all_trace_fusion_of_persistence
#print axioms review_trace_persistence_of_sourceLetter
#print axioms review_all_trace_fusion_of_sourceLetter
#print axioms review_large_set_homogeneous_of_sourceLetter
#print axioms review_fixedStemPigeonhole_of_sourceLetter
#print axioms review_fixedStemPigeonhole
#print axioms fixedStemPigeonhole_review
#print axioms ellentuck_review
#print axioms fatTreeFixedStemPigeonhole
#print axioms fatTreeA4
#print axioms fatTreeAbstractRamseySpace
#print axioms fatTreeEllentuck

/- These endpoint types must not silently acquire A4, good-pair,
saturation, positivity, or root-cut premises. -/
section InterfaceGuard
open SuccessorTree SuccessorTree.SMTree
universe u1 v1 w1 z1
variable {T : Type u1} {Label : Type v1} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
example {c : Nat} {C : Type w1} [Fintype C] [Nonempty C]
    {κ : Type z1} [Fintype κ]
    (H : SMTree S) (U : SuccessorTree.SMTree.FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (hpos : 0 < U.cut a) (chi : AM H c 1 → κ) :
    Nonempty (ReviewFanLine H U a trace hend chi) :=
  exists_reviewFanLine_positive H U a trace hend hpos chi

example (H : SMTree S) : FixedStemPigeonhole H :=
  fixedStemPigeonhole_review H

example (H : SMTree S) : FixedStemPigeonhole H :=
  fatTreeFixedStemPigeonhole H

example (H : SMTree S)
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : SuccessorTree.SMTree.FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    (O : Set ((approximationSystem H).Approx (n + 1))) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d B ∧
      ((approximationSystem H).oneStepApproximations a V ⊆ O ∨
        Disjoint ((approximationSystem H).oneStepApproximations a V) O) :=
  fatTreeA4 H a B hd O

noncomputable example (H : SMTree S) :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  fatTreeAbstractRamseySpace H

example (H : SMTree S) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  ellentuck_review H

example (H : SMTree S) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  fatTreeEllentuck H
end InterfaceGuard
