import Mathlib.Tactic

/-!
# Level sets in a decreasing envelope run

These lemmas use only the recursion on sets of natural numbers. They do not
mention trees, maps, E1, or any monoid axiom. Keep this bookkeeping separate
from the invariant asserting that an output map covers a closure.
-/

set_option autoImplicit false

namespace SuccessorTree.SMTree.Envelope

/-- A level set obtained by optionally inserting each descending index stays
inside the interval from that index to the chosen top level. -/
theorem levelSets_mem_bounds
    (I : Nat → Set Nat) (ell : Nat)
    (htop : I ell = {ell})
    (hstep : ∀ i, i < ell →
      I i = I (i + 1) ∨ I i = insert i (I (i + 1))) :
    ∀ i, i ≤ ell → ∀ q ∈ I i, i ≤ q ∧ q ≤ ell := by
  have main : ∀ d i, ell - i = d → i ≤ ell →
      ∀ q ∈ I i, i ≤ q ∧ q ≤ ell := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hdi hi q hq
      by_cases hieq : i = ell
      · subst i
        rw [htop, Set.mem_singleton_iff] at hq
        subst q
        exact ⟨le_rfl, le_rfl⟩
      · have hilt : i < ell := by omega
        have hsmall : ell - (i + 1) < d := by omega
        have hnext := ih (ell - (i + 1)) hsmall (i + 1) rfl (by omega)
        rcases hstep i hilt with hkeep | hinsert
        · rw [hkeep] at hq
          have hb := hnext q hq
          exact ⟨by omega, hb.2⟩
        · rw [hinsert, Set.mem_insert_iff] at hq
          rcases hq with rfl | hq
          · exact ⟨le_rfl, hi⟩
          · have hb := hnext q hq
            exact ⟨by omega, hb.2⟩
  intro i hi
  exact main (ell - i) i rfl hi

/-- Removing the current descending index recovers the preceding stage. -/
theorem levelSets_next_eq
    (I : Nat → Set Nat) (ell : Nat)
    (htop : I ell = {ell})
    (hstep : ∀ i, i < ell →
      I i = I (i + 1) ∨ I i = insert i (I (i + 1)))
    (i : Nat) (hi : i < ell) :
    I (i + 1) = {q | q ∈ I i ∧ i < q} := by
  have hgt : ∀ q ∈ I (i + 1), i < q := by
    intro q hq
    have hb := levelSets_mem_bounds I ell htop hstep (i + 1) (by omega) q hq
    omega
  ext q
  change q ∈ I (i + 1) ↔ q ∈ I i ∧ i < q
  rcases hstep i hi with hkeep | hinsert
  · rw [hkeep]
    exact ⟨fun hq => ⟨hq, hgt q hq⟩, fun hq => hq.1⟩
  · rw [hinsert, Set.mem_insert_iff]
    constructor
    · intro hq
      exact ⟨Or.inr hq, hgt q hq⟩
    · rintro ⟨hqi | hq, hiq⟩
      · omega
      · exact hq

/-- Every intermediate set is the corresponding tail of the final set. -/
theorem levelSets_eq_final_tail
    (I : Nat → Set Nat) (ell : Nat)
    (htop : I ell = {ell})
    (hstep : ∀ i, i < ell →
      I i = I (i + 1) ∨ I i = insert i (I (i + 1))) :
    ∀ i, i ≤ ell → I i = {q | q ∈ I 0 ∧ i ≤ q} := by
  intro i
  induction i with
  | zero =>
    intro _
    ext q
    simp
  | succ i ih =>
    intro hi
    rw [levelSets_next_eq I ell htop hstep i (by omega), ih (by omega)]
    ext q
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hq, _⟩, hiq⟩
      exact ⟨hq, by omega⟩
    · rintro ⟨hq, hiq⟩
      exact ⟨⟨hq, by omega⟩, by omega⟩

end SuccessorTree.SMTree.Envelope
