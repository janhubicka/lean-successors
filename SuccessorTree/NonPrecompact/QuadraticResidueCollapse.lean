import SuccessorTree.NonPrecompact.ResidueAlgebra

/-!
# Collapse of quadratic moments in the residue algebra

For q = 2^s and d = q - 1, once the lower moments are even and the
middle moment is odd, the moment expansion in F₂[Z/qZ] collapses to t^d.
Higher terms vanish because t^q = 0.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- If q = 2^s and d = q - 1, then a finite moment sum with even lower
moments and odd middle moment is exactly t^d in the residue algebra. -/
theorem residueMomentSum_eq_middle_power
    (s N : ℕ)
    (M : ℕ → ℕ)
    (hmid : Odd (M (2 ^ s - 1)))
    (hlow : ∀ k, k < 2 ^ s - 1 → Even (M k))
    (hN : 2 ^ s - 1 ≤ N) :
    (∑ k ∈ Finset.range (N + 1),
      residueCoeff (2 ^ s) (M k : F2) *
        residueT (2 ^ s) ^ k) =
      residueT (2 ^ s) ^ (2 ^ s - 1) := by
  let d := 2 ^ s - 1
  have hqpos : 0 < 2 ^ s := pow_pos (by decide) _
  have hdq : d + 1 = 2 ^ s := by
    dsimp [d]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))
  calc
    (∑ k ∈ Finset.range (N + 1),
      residueCoeff (2 ^ s) (M k : F2) *
        residueT (2 ^ s) ^ k) =
        residueCoeff (2 ^ s) (M d : F2) *
          residueT (2 ^ s) ^ d := by
      apply Finset.sum_eq_single d
      · intro k hk hne
        rcases lt_or_gt_of_ne hne with hkd | hdk
        · have heven : (M k : F2) = 0 :=
            (hlow k (by simpa [d] using hkd)).natCast_zmod_two
          simp [heven, residueCoeff]
        · have hqk : 2 ^ s ≤ k := by
            rw [← hdq]
            exact Nat.succ_le_iff.mpr hdk
          have htzero :
              residueT (2 ^ s) ^ k = 0 :=
            pow_eq_zero_of_le hqk (residueT_pow_two_pow_eq_zero s)
          simp [htzero]
      · intro hdnot
        exfalso
        apply hdnot
        simp [Finset.mem_range, d, hN]
    _ = residueT (2 ^ s) ^ (2 ^ s - 1) := by
      have hodd : (M d : F2) = 1 := by
        apply ZMod.natCast_eq_one_iff_odd.mpr
        simpa [d] using hmid
      rw [hodd]
      simp [residueCoeff, d]

end SuccessorTree.NonPrecompact
