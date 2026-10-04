import Mathlib

/-!
# Integer arithmetic for the quadratic Gauss sum

A small arithmetic step from the symplectic quadratic-residue proof:
an integer whose square is 2^(2d) is ±2^d.
-/

namespace SuccessorTree.NonPrecompact

/-- If an integer square is the even power 2^(2d), the integer is ±2^d. -/
theorem int_eq_pow_two_or_neg_of_sq_eq
    (T : ℤ) (d : ℕ)
    (h : T ^ 2 = (2 : ℤ) ^ (2 * d)) :
    T = (2 : ℤ) ^ d ∨ T = -((2 : ℤ) ^ d) := by
  have h' : T ^ 2 = ((2 : ℤ) ^ d) ^ 2 := by
    calc
      T ^ 2 = (2 : ℤ) ^ (2 * d) := h
      _ = (2 : ℤ) ^ (d * 2) := by rw [Nat.mul_comm]
      _ = ((2 : ℤ) ^ d) ^ 2 := by
        exact pow_mul (2 : ℤ) d 2
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h'

end SuccessorTree.NonPrecompact
