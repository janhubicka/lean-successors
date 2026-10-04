import Mathlib

/-!
# Parity consequence of the quadratic Gauss congruence

This file isolates the final elementary arithmetic implication used in the
symplectic quadratic-residue proof.  If T = ±2^d and
T ≡ (-2)^d M modulo 2^(d+1), then M is odd.
-/

namespace SuccessorTree.NonPrecompact

/-- Cancelling the common 2^d factor in the quadratic Gauss congruence shows
that the middle binomial moment is odd. -/
theorem odd_of_gauss_congruence
    (T : ℤ) (M d : ℕ)
    (hT : T = (2 : ℤ) ^ d ∨ T = -((2 : ℤ) ^ d))
    (hmod :
      T ≡ (-2 : ℤ) ^ d * (M : ℤ)
        [ZMOD (2 : ℤ) ^ (d + 1)]) :
    Odd M := by
  let c : ℤ := (2 : ℤ) ^ d
  let s : ℤ := (-1 : ℤ) ^ d
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hneg : (-1 : ℤ) ≡ 1 [ZMOD 2] := by
    norm_num [Int.ModEq]
  have hs : s ≡ 1 [ZMOD 2] := by
    dsimp [s]
    simpa using hneg.pow d
  have hsM : s * (M : ℤ) ≡ (M : ℤ) [ZMOD 2] := by
    simpa using
      hs.mul (Int.ModEq.rfl : (M : ℤ) ≡ (M : ℤ) [ZMOD 2])

  have hfactor :
      (-2 : ℤ) ^ d * (M : ℤ) = c * (s * (M : ℤ)) := by
    dsimp [c, s]
    rw [show (-2 : ℤ) = (-1 : ℤ) * 2 by norm_num, mul_pow]
    ring

  have hmodulus :
      (2 : ℤ) ^ (d + 1) = c * 2 := by
    dsimp [c]
    rw [pow_succ]

  have hM : (M : ℤ) ≡ 1 [ZMOD 2] := by
    rcases hT with hplus | hminus
    · have hcancel : (1 : ℤ) ≡ s * (M : ℤ) [ZMOD 2] := by
        apply Int.ModEq.mul_left_cancel' hc
        rw [← hmodulus, ← hfactor]
        simpa [c, hplus] using hmod
      exact hsM.symm.trans hcancel.symm
    · have hcancel : (-1 : ℤ) ≡ s * (M : ℤ) [ZMOD 2] := by
        apply Int.ModEq.mul_left_cancel' hc
        rw [← hmodulus, ← hfactor]
        have hminus' : T = c * (-1) := by
          rw [hminus]
          dsimp [c]
          ring
        simpa [hminus'] using hmod
      exact hsM.symm.trans (hcancel.symm.trans hneg)

  have hz : ((M : ℤ) : ZMod 2) = 1 := by
    exact (ZMod.intCast_eq_intCast_iff (M : ℤ) 1 2).2 hM
  have hn : (M : ZMod 2) = 1 := by
    norm_cast at hz ⊢
  exact ZMod.natCast_eq_one_iff_odd.mp hn

end SuccessorTree.NonPrecompact
