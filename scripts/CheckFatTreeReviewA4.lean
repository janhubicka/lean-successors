import SuccessorTree.FatTree.A4ReviewLine

open SuccessorTree.SMTree.FatTree

#check persistentAcceptedPair_of_dense_pairs
#check review_fixedStemPigeonhole_positive
#check ProfileReplayState.review_common_tail_replays
#check ProfileReplayState.review_raw_fan_represented
#check ProfileReplayState.review_exists_profile_fan_homogeneity
#check exists_reviewFanLine_positive
#print axioms oneBlockOccurs_of_reduces
#print axioms oneBlockOccurs_of_pair
#print axioms appendRow_injective
#print axioms headsAtDepth_finite
#print axioms eliminate_accepted_pair_at_depth
#print axioms eliminate_accepted_pair_batch
#print axioms eliminate_all_accepted_pairs_at_depth
#print axioms persistentAcceptedPair_of_dense_pairs
#print axioms review_trace_persistence
#print axioms review_all_trace_fusion
#print axioms review_goodRows_transport
#print axioms review_good_row_of_good_prefix
#print axioms review_large_set_homogeneous
#print axioms review_fixedStemPigeonhole_positive
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
#print axioms exists_reviewFanLine_positive

/- The local endpoint must elaborate from the SM-tree data and a positive
source cut. Adding an A4, good-pair, or saturation premise must break this
type-level regression test rather than silently strengthen the theorem. -/
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
end InterfaceGuard
