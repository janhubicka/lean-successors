import SuccessorTree.EnvelopeTheorem

/-!
These statement regressions deliberately provide no E1 or bound on X.
The first section does not even have an underlying tree. This is distinct
from an axiom report: explicit theorem hypotheses must also be audited.
-/

set_option autoImplicit false

open SuccessorTree SuccessorTree.SMTree SuccessorTree.SMTree.Envelope

section PureLevelSets

example (I : Nat → Set Nat) (ell : Nat)
    (htop : I ell = {ell})
    (hstep : ∀ i, i < ell →
      I i = I (i + 1) ∨ I i = insert i (I (i + 1)))
    (i : Nat) (hi : i ≤ ell) :
    I i = {q | q ∈ I 0 ∧ i ≤ q} :=
  levelSets_eq_final_tail I ell htop hstep i hi

example (I : Nat → Set Nat) (htop : I 0 = {0}) :
    ∀ q ∈ I 0, 0 ≤ q ∧ q ≤ 0 := by
  exact levelSets_mem_bounds I 0 htop (by intro i hi; omega) 0 le_rfl

end PureLevelSets

section Runs

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

example (H : SMTree S) (X : Set T) (ell i : Nat)
    (R : AlgorithmRun H X ell) (hi : i ≤ ell) :
    R.I i = {q | q ∈ R.I 0 ∧ i ≤ q} :=
  R.I_eq_final_tail_of_run i hi

-- The recursion is legitimate on the empty set, although the nonempty
-- minimal-envelope theorem is not applicable to such an arbitrary-top run.
example (H : SMTree S) (ell i : Nat)
    (R : AlgorithmRun H (∅ : Set T) ell) (hi : i < ell) :
    R.I (i + 1) = {q | q ∈ R.I i ∧ i < q} :=
  R.nextI_eq_of_run i hi

example (H : SMTree S) (X : Set T) (ell : Nat)
    (R : AlgorithmRun H X ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (E : MMap H) (m : Nat) (hEnv : IsPrefixEnvelope E.map m X) :
    ∀ ⦃i : Nat⦄, i ∈ R.I 0 → RepresentedBefore H E.map m i :=
  R.finalLevels_subset_competitor_of_run hTop E m hEnv

-- Both old and new finite-envelope names continue to denote the same predicate.
example (H : SMTree S) (X : Set T) (m : Nat) (a : AM H 0 m) :
    IsAMEnvelope H a X ↔ AlgorithmRun.IsAMEnvelope H a X := Iff.rfl

end Runs

#print axioms SuccessorTree.SMTree.Envelope.levelSets_mem_bounds
#print axioms SuccessorTree.SMTree.Envelope.levelSets_next_eq
#print axioms SuccessorTree.SMTree.Envelope.levelSets_eq_final_tail
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.I_mem_bounds
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.nextI_eq_of_run
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.I_eq_final_tail_of_run
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.finalLevel_interesting_of_run
#print axioms SuccessorTree.SMTree.Envelope.AlgorithmRun.finalLevels_subset_competitor_of_run
