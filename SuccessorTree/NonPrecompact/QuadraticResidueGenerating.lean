import SuccessorTree.NonPrecompact.ResidueAlgebra

/-!
# Residue generating functions for quadratic weights

This file formalises the group-algebra bridge in the symplectic
quadratic-residue proof.

For a finite family of natural weights Q(x), the residue generating
function sum_x Z^{Q(x)} is expanded in powers of t = 1 + Z with coefficients
given by the binomial moments.  Its coefficient at a residue r is the parity
of the number of x with Q(x) congruent to r modulo q.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The residue generating function attached to a finite natural-valued
weight. -/
noncomputable def residueWeightGenerating
    (q : ℕ) {V : Type*} [Fintype V] (Q : V → ℕ) :
    ResidueAlgebra q :=
  ∑ x : V, residueZ q ^ Q x

/-- Natural-number scalars in the residue algebra are exactly the coefficient
embedding after reduction modulo two. -/
theorem natCast_residueAlgebra_eq_residueCoeff
    (q n : ℕ) :
    (n : ResidueAlgebra q) = residueCoeff q (n : F2) := by
  rfl

/-- In characteristic two, Z = t + 1. -/
theorem residueZ_eq_residueT_add_one (q : ℕ) :
    residueZ q = residueT q + 1 := by
  rw [residueT]
  have h11 : (1 + 1 : ResidueAlgebra q) = 0 :=
    CharTwo.add_self_eq_zero.mpr rfl
  calc
    residueZ q = residueZ q + 0 := by simp
    _ = residueZ q + (1 + 1) := by rw [h11]
    _ = (1 + residueZ q) + 1 := by ac_rfl

/-- Binomial expansion of a single residue monomial in powers of t. -/
theorem residueZ_pow_eq_sum_choose_residueT
    (q n : ℕ) :
    residueZ q ^ n =
      ∑ k ∈ Finset.range (n + 1),
        residueCoeff q (n.choose k : F2) * residueT q ^ k := by
  rw [residueZ_eq_residueT_add_one]
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow, mul_one]
  rw [← natCast_residueAlgebra_eq_residueCoeff]
  ac_rfl

/-- Extend the pointwise residue-binomial sum to any common upper bound. -/
theorem sum_choose_residueT_eq_sum_range_of_le
    (q n N : ℕ) (hn : n ≤ N) :
    (∑ k ∈ Finset.range (n + 1),
      residueCoeff q (n.choose k : F2) * residueT q ^ k) =
      ∑ k ∈ Finset.range (N + 1),
        residueCoeff q (n.choose k : F2) * residueT q ^ k := by
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ hn)
  · intro k hkN hkn
    have hnk : n < k := by
      have hnot : ¬ k < n + 1 := by
        simpa [Finset.mem_range] using hkn
      omega
    rw [Nat.choose_eq_zero_of_lt hnk]
    simp [residueCoeff]

/-- The residue generating function is the finite t-expansion whose
coefficients are the binomial moments reduced modulo two. -/
theorem residueWeightGenerating_eq_sum_binomialMoments
    (q : ℕ) {V : Type*} [Fintype V]
    (Q : V → ℕ) (N : ℕ)
    (hQ : ∀ x, Q x ≤ N) :
    residueWeightGenerating q Q =
      ∑ k ∈ Finset.range (N + 1),
        residueCoeff q
          ((∑ x : V, (Q x).choose k : ℕ) : F2) *
          residueT q ^ k := by
  unfold residueWeightGenerating
  calc
    (∑ x : V, residueZ q ^ Q x) =
        ∑ x : V, ∑ k ∈ Finset.range (N + 1),
          residueCoeff q ((Q x).choose k : F2) *
            residueT q ^ k := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [residueZ_pow_eq_sum_choose_residueT]
      exact sum_choose_residueT_eq_sum_range_of_le
        q (Q x) N (hQ x)
    _ = ∑ k ∈ Finset.range (N + 1), ∑ x : V,
          residueCoeff q ((Q x).choose k : F2) *
            residueT q ^ k := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (N + 1),
          residueCoeff q
            ((∑ x : V, (Q x).choose k : ℕ) : F2) *
            residueT q ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_mul, ← residueCoeff_fintype_sum]
      congr 2
      norm_cast

/-- The coefficient of the residue generating function at r is the parity of
the number of vectors whose weight is congruent to r modulo q. -/
theorem coeff_residueWeightGenerating_eq_card_filter
    (q : ℕ) {V : Type*} [Fintype V]
    (Q : V → ℕ) (r : ZMod q) :
    (residueWeightGenerating q Q).coeff r =
      (((Finset.univ : Finset V).filter
        (fun x => (Q x : ZMod q) = r)).card : F2) := by
  classical
  unfold residueWeightGenerating
  rw [AddMonoidAlgebra.coeff_sum]
  simp_rw [residueZ_pow, AddMonoidAlgebra.coeff_single]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  have hcast :
      Q x • (1 : ZMod q) = (Q x : ZMod q) := by
    simp [nsmul_eq_mul]
  rw [hcast]
  by_cases h : (Q x : ZMod q) = r
  · simp [h]
  · simp [h]

/-- If the residue generating function is t^(q-1), then every residue fibre
has odd cardinality. -/
theorem residueFibres_odd_of_generating_eq_middlePower
    (s : ℕ) {V : Type*} [Fintype V]
    (Q : V → ℕ)
    (hgen :
      residueWeightGenerating (2 ^ s) Q =
        residueT (2 ^ s) ^ (2 ^ s - 1))
    (r : ZMod (2 ^ s)) :
    Odd (((Finset.univ : Finset V).filter
      (fun x => (Q x : ZMod (2 ^ s)) = r)).card) := by
  have hcoeff := congrArg
    (fun y : ResidueAlgebra (2 ^ s) => y.coeff r) hgen
  rw [coeff_residueWeightGenerating_eq_card_filter] at hcoeff
  rw [coeff_residueT_pow_pred_two_pow_eq_one] at hcoeff
  exact ZMod.natCast_eq_one_iff_odd.mp hcoeff

end SuccessorTree.NonPrecompact
