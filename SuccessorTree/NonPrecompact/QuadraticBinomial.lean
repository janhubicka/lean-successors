import Mathlib

/-!
# Binomial expansion for the quadratic residue argument

The circulation proof uses the ordinary binomial identity
  (-1)^Q = (1 - 2)^Q = sum_k choose(Q,k) (-2)^k
and then sums it over a finite vector space.  This file isolates that
arithmetic identity for any finite family of bounded natural weights.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Pointwise integer binomial expansion of (-1)^q. -/
theorem neg_one_pow_eq_sum_choose_neg_two (q : ℕ) :
    (-1 : ℤ) ^ q =
      ∑ k ∈ Finset.range (q + 1),
        (q.choose k : ℤ) * (-2 : ℤ) ^ k := by
  have h := add_pow (-2 : ℤ) 1 q
  simpa [mul_assoc, mul_comm, mul_left_comm] using h

/-- Extend the pointwise binomial sum to any larger upper bound; the added
binomial coefficients vanish. -/
theorem sum_choose_neg_two_eq_sum_range_of_le
    (q N : ℕ) (hq : q ≤ N) :
    (∑ k ∈ Finset.range (q + 1),
        (q.choose k : ℤ) * (-2 : ℤ) ^ k) =
      ∑ k ∈ Finset.range (N + 1),
        (q.choose k : ℤ) * (-2 : ℤ) ^ k := by
  apply Finset.sum_subset
  · exact Finset.range_mono (Nat.succ_le_succ hq)
  · intro k hkN hkq
    have hklt : q < k := by
      have hknot : ¬ k < q + 1 := by
        simpa [Finset.mem_range] using hkq
      omega
    rw [Nat.choose_eq_zero_of_lt hklt]
    simp

/-- Summing the pointwise binomial theorem over a finite family gives the
moment expansion used in the quadratic residue proof. -/
theorem sum_neg_one_pow_eq_sum_binomial_moments
    {V : Type*} [Fintype V]
    (Q : V → ℕ) (N : ℕ)
    (hQ : ∀ x, Q x ≤ N) :
    (∑ x : V, (-1 : ℤ) ^ Q x) =
      ∑ k ∈ Finset.range (N + 1),
        (-2 : ℤ) ^ k * ∑ x : V, (Q x).choose k := by
  calc
    (∑ x : V, (-1 : ℤ) ^ Q x) =
        ∑ x : V, ∑ k ∈ Finset.range (N + 1),
          ((Q x).choose k : ℤ) * (-2 : ℤ) ^ k := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [neg_one_pow_eq_sum_choose_neg_two]
      exact sum_choose_neg_two_eq_sum_range_of_le (Q x) N (hQ x)
    _ = ∑ k ∈ Finset.range (N + 1), ∑ x : V,
          ((Q x).choose k : ℤ) * (-2 : ℤ) ^ k := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (N + 1),
          (-2 : ℤ) ^ k * ∑ x : V, (Q x).choose k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_mul]
      push_cast
      ring

end SuccessorTree.NonPrecompact
