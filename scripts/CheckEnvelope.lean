import SuccessorTree.EnvelopeTheorem

-- These regressions run in both existing workflows without changing their
-- 31-endpoint inventory. Those endpoints transitively audit the new proofs.
set_option autoImplicit false
open SuccessorTree SuccessorTree.SMTree SuccessorTree.SMTree.Envelope

example (I : Nat → Set Nat) (ell : Nat)
    (htop : I ell = {ell})
    (hstep : ∀ i, i < ell →
      I i = I (i + 1) ∨ I i = insert i (I (i + 1))) :
    ∀ i, i ≤ ell → I i = {q | q ∈ I 0 ∧ i ≤ q} :=
  levelSets_eq_final_tail I ell htop hstep

section HypothesisBoundary
universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

example (H : SMTree S) (ell i : Nat)
    (R : AlgorithmRun H (∅ : Set T) ell) (hi : i ≤ ell) :
    R.I i = {q | q ∈ R.I 0 ∧ i ≤ q} :=
  R.I_eq_final_tail_of_run i hi

example (H : SMTree S) (X : Set T) (ell : Nat)
    (R : AlgorithmRun H X ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (E : MMap H) (m : Nat) (hEnv : IsPrefixEnvelope E.map m X) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 → RepresentedBefore H E.map m i :=
  R.finalLevels_subset_competitor_of_run hTop E m hEnv
end HypothesisBoundary

#print axioms SuccessorTree.SMTree.Envelope.range_meetClosed
#print axioms SuccessorTree.SMTree.Envelope.range_parameterClosed
#print axioms SuccessorTree.SMTree.Envelope.closure_subset_range
#print axioms SuccessorTree.SMTree.Envelope.closure_finite_of_bounded
#print axioms SuccessorTree.SMTree.Envelope.nextPrefix_eq_of_no_meet
#print axioms SuccessorTree.SMTree.Envelope.subset_range_of_oneLevel
#print axioms SuccessorTree.SMTree.Envelope.preimage_subset_range_of_bounded_indexed
#print axioms SuccessorTree.SMTree.Envelope.stageInvariant_interesting
#print axioms SuccessorTree.SMTree.Envelope.stageInvariant_noninteresting
#print axioms SuccessorTree.SMTree.Envelope.stageFullInvariant_base
#print axioms SuccessorTree.SMTree.Envelope.stageFullInvariant_noninteresting
#print axioms SuccessorTree.SMTree.Envelope.stageFullInvariant_skips_iff
#print axioms SuccessorTree.SMTree.Envelope.prefixEnvelope_closure
#print axioms SuccessorTree.SMTree.Envelope.exists_oneLevel_skip_extension_of_gap
#print axioms SuccessorTree.SMTree.Envelope.representedBefore_of_interesting
#print axioms SuccessorTree.SMTree.Envelope.oneLevel_preimage_unique_below
#print axioms SuccessorTree.SMTree.Envelope.preimage_eq_of_oneLevel
#print axioms SuccessorTree.SMTree.Envelope.embeddingType_noninteresting_choice_independent
#print axioms SuccessorTree.SMTree.Envelope.algorithmLevels_subset_competitor
#print axioms SuccessorTree.SMTree.Envelope.card_prefixLevels
#print axioms SuccessorTree.SMTree.Envelope.card_le_competing_height
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.fullInvariant
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.finalLevel_interesting
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.finalLevels_subset_competitor
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.I_eq
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.embeddingType_eq
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.minimal_output_height
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.minimal_output_height_AM
#print axioms SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
#print axioms SuccessorTree.SMTree.Envelope.algorithmRun_nonempty
#print axioms SuccessorTree.SMTree.Envelope.exists_minimalEnvelope
