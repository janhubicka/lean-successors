import Mathlib

/-!
# Modular truncation of the quadratic binomial moment expansion

This file isolates the arithmetic step
  sum_k (-2)^k M_k ≡ (-2)^d M_d  mod 2^(d+1).
For k < d, the required divisibility comes from the stronger moment
divisibility 2^(2d-2k) | M_k.  For k > d it comes directly from the
visible factor (-2)^k.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

private theorem two_dvd_neg_two : (2 : ℤ) ∣ (-2 : ℤ) := by
  exact ⟨-1, by norm_num⟩

/-- A lower binomial term vanishes modulo 2^(d+1) when its moment has the
manuscript's stronger divisibility. -/
theorem neg_two_pow_mul_modEq_zero_of_lt
    (k d : ℕ) (M : ℤ)
    (hkd : k < d)
    (hM : (2 : ℤ) ^ (2 * d - 2 * k) ∣ M) :
    (-2 : ℤ) ^ k * M ≡ 0 [ZMOD (2 : ℤ) ^ (d + 1)] := by
  rw [Int.modEq_zero_iff_dvd]
  have hsign :
      (2 : ℤ) ^ k ∣ (-2 : ℤ) ^ k :=
    pow_dvd_pow_of_dvd two_dvd_neg_two k
  have hprod :
      (2 : ℤ) ^ k * (2 : ℤ) ^ (2 * d - 2 * k) ∣
        (-2 : ℤ) ^ k * M :=
    mul_dvd_mul hsign hM
  have hexp :
      k + (2 * d - 2 * k) = 2 * d - k := by
    omega
  have hle : d + 1 ≤ 2 * d - k := by
    omega
  have hpow :
      (2 : ℤ) ^ (d + 1) ∣ (2 : ℤ) ^ (2 * d - k) :=
    pow_dvd_pow (2 : ℤ) hle
  apply hpow.trans
  rw [← hexp, pow_add]
  exact hprod

/-- A higher binomial term vanishes modulo 2^(d+1) from the visible power
of two in (-2)^k. -/
theorem neg_two_pow_mul_modEq_zero_of_gt
    (k d : ℕ) (M : ℤ)
    (hdk : d < k) :
    (-2 : ℤ) ^ k * M ≡ 0 [ZMOD (2 : ℤ) ^ (d + 1)] := by
  rw [Int.modEq_zero_iff_dvd]
  have hle : d + 1 ≤ k := Nat.succ_le_iff.mpr hdk
  have hpow :
      (2 : ℤ) ^ (d + 1) ∣ (2 : ℤ) ^ k :=
    pow_dvd_pow (2 : ℤ) hle
  have hsign :
      (2 : ℤ) ^ k ∣ (-2 : ℤ) ^ k :=
    pow_dvd_pow_of_dvd two_dvd_neg_two k
  exact (hpow.trans hsign).mul_right M

/-- If lower moments have the quadratic divisibility, all terms except the
middle one disappear modulo 2^(d+1). -/
theorem sum_neg_two_pow_mul_modEq_middle
    (M : ℕ → ℤ) (d N : ℕ)
    (hdN : d ≤ N)
    (hlow :
      ∀ k, k < d →
        (2 : ℤ) ^ (2 * d - 2 * k) ∣ M k) :
    (∑ k ∈ Finset.range (N + 1), (-2 : ℤ) ^ k * M k) ≡
      (-2 : ℤ) ^ d * M d
        [ZMOD (2 : ℤ) ^ (d + 1)] := by
  apply Int.sum_modEq_single
  · intro hdnot
    exfalso
    apply hdnot
    simp [Finset.mem_range, hdN]
  · intro k hk hne
    have hkN : k ≤ N := by
      simpa [Finset.mem_range] using hk
    rcases lt_or_gt_of_ne hne with hkd | hdk
    · exact neg_two_pow_mul_modEq_zero_of_lt k d (M k) hkd
        (hlow k hkd)
    · exact neg_two_pow_mul_modEq_zero_of_gt k d (M k) hdk

end SuccessorTree.NonPrecompact
