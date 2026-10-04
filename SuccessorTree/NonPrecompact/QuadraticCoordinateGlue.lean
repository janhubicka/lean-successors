import SuccessorTree.NonPrecompact.QuadraticGauss
import SuccessorTree.NonPrecompact.QuadraticMoments

/-!
# Coordinate glue for the quadratic residue argument

Small lemmas connecting the matrix/affine coordinate weight to the
character-sum and divisibility statements used in the manuscript.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Matrix

/-- Each Boolean coordinate contributes at most one to the ordinary weight. -/
theorem bilinearWeight_le_card
    {d n : ℕ}
    (A B : Matrix (Fin d) (Fin n) F2)
    (c e : Fin n → F2)
    (x y : Fin d → F2) :
    bilinearWeight A B c e x y ≤ n := by
  unfold bilinearWeight
  calc
    (∑ i : Fin n, (pairBit A B c e i x y).val) ≤
        ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      have hlt := ZMod.val_lt (pairBit A B c e i x y)
      omega
    _ = n := by simp

/-- The sign character of the mod-two reduction of a natural number is
exactly (-1)^m. -/
theorem f2Sign_natCast_eq_neg_one_pow (m : ℕ) :
    f2Sign (m : F2) = (-1 : ℤ) ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Nat.cast_succ, f2Sign_add, ih, f2Sign_one, pow_succ]

/-- The abstract quadratic Gauss sum of the mod-two reduction of a natural
weight is the ordinary integer sign sum used in the manuscript. -/
theorem quadraticGaussSum_natWeight
    {V : Type*} [Fintype V]
    (Q : V → ℕ) :
    quadraticGaussSum (fun x => (Q x : F2)) =
      ∑ x : V, (-1 : ℤ) ^ Q x := by
  unfold quadraticGaussSum
  apply Finset.sum_congr rfl
  intro x hx
  exact f2Sign_natCast_eq_neg_one_pow (Q x)

/-- The standard binary coordinate space of dimension D has cardinality
2^D. -/
theorem card_fin_fun_f2 (D : ℕ) :
    Fintype.card (Fin D → F2) = 2 ^ D := by
  rw [Fintype.card_fun, Fintype.card_fin]
  norm_num [ZMod.card]

/-- The quadratic lower-moment divisibility implies evenness whenever
k < d. -/
theorem even_of_quadratic_moment_divisibility
    (d k M : ℕ)
    (hkd : k < d)
    (hdiv : 2 ^ (2 * d - 2 * k) ∣ M) :
    Even M := by
  rw [Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero]
  have hpos : 1 ≤ 2 * d - 2 * k := by omega
  simpa using (pow_dvd_pow 2 hpos).trans hdiv

/-- Cast a natural power-of-two divisibility statement to the integers. -/
theorem int_pow_two_dvd_natCast_of_nat_dvd
    (m n : ℕ)
    (h : 2 ^ m ∣ n) :
    (2 : ℤ) ^ m ∣ (n : ℤ) := by
  exact Int.ofNat_dvd.mpr h

end SuccessorTree.NonPrecompact
