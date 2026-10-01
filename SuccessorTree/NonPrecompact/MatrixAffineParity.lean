import SuccessorTree.NonPrecompact.AffineParity

/-!
# Matrix affine fibres over F₂

These lemmas turn the affine-fibre parity statement into the two matrix
forms used in the BANANA residue colouring.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- An underdetermined matrix system over `F₂` has an even number of
solutions. -/
theorem even_card_matrixAffineFiber_of_lt
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) F2) (b : Fin m → F2)
    (hmn : m < n) :
    Even (Nat.card (affineFiber M.mulVecLin b)) := by
  apply even_card_affineFiber_of_finrank_lt
  simpa only [Module.finrank_pi, Fintype.card_fin] using hmn

/-- For a square matrix over `F₂`, the parity of every affine fibre is
the determinant. -/
theorem natCast_card_affineFiber_eq_det
    {n : ℕ} (M : Matrix (Fin n) (Fin n) F2) (b : Fin n → F2) :
    (Nat.card (affineFiber M.mulVecLin b) : F2) = M.det := by
  by_cases hdet : M.det = 0
  · rw [hdet, ZMod.natCast_eq_zero_iff_even]
    have hker : LinearMap.ker M.mulVecLin ≠ ⊥ := by
      have hlin : LinearMap.det (Matrix.toLin' M) = 0 := by
        simpa using hdet
      have hk :=
        (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hlin
      simpa [Matrix.toLin'_apply'] using hk
    by_cases hne : Nonempty (affineFiber M.mulVecLin b)
    · let x0 : affineFiber M.mulVecLin b := Classical.choice hne
      rw [affineFiber_card_eq_ker_card M.mulVecLin b x0]
      exact even_card_ker_of_ne_bot M.mulVecLin hker
    · letI : IsEmpty (affineFiber M.mulVecLin b) := ⟨fun x => hne ⟨x⟩⟩
      rw [(Finite.card_eq_zero_iff).2 inferInstance]
      simp
  · have hMunit : IsUnit M := by
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.mpr hdet
    have hinj : Function.Injective M.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr hMunit
    have hsurj : Function.Surjective M.mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr hMunit
    have hnonempty : Nonempty (affineFiber M.mulVecLin b) := by
      obtain ⟨x, hx⟩ := hsurj b
      exact ⟨⟨x, hx⟩⟩
    have hsub : Subsingleton (affineFiber M.mulVecLin b) :=
      ⟨fun x y => Subtype.ext (hinj (x.2.trans y.2.symm))⟩
    have hcard : Nat.card (affineFiber M.mulVecLin b) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, hnonempty⟩
    have hdet1 : M.det = 1 := by
      have hpos : 0 < M.det.val := (ZMod.val_pos).2 hdet
      have hlt : M.det.val < 2 := ZMod.val_lt M.det
      apply ZMod.val_injective
      simp only [ZMod.val_one]
      omega
    rw [hcard, hdet1]
    norm_num

end SuccessorTree.NonPrecompact
