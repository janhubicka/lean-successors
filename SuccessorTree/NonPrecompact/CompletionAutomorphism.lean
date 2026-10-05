import SuccessorTree.NonPrecompact.Completion
import SuccessorTree.NonPrecompact.PerfectHomogeneity
import SuccessorTree.NonPrecompact.BananaDirectSum

/-!
# Canonical automorphisms of perfect completions

This file formalises the finite-linear-algebra action used in the coherent
EPPA proof for BANANA.  An automorphism of a finite source pairing acts on
its perfect completion by

  f ⊕ (g⁻¹)ᵗ

on the left completion coordinates; the right action is the corresponding
contragredient.  The resulting automorphism extends the original maps on
both completion images.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- Direct sum of two linear equivalences on binary coordinate spaces. -/
noncomputable def directSumLinearEquiv
    {m₁ m₂ n₁ n₂ : ℕ}
    (f : (Fin m₁ → F2) ≃ₗ[F2] (Fin n₁ → F2))
    (g : (Fin m₂ → F2) ≃ₗ[F2] (Fin n₂ → F2)) :
    (Fin (m₁ + m₂) → F2) ≃ₗ[F2] (Fin (n₁ + n₂) → F2) where
  toLinearMap := directSumLinearMap f.toLinearMap g.toLinearMap
  invFun := directSumLinearMap f.symm.toLinearMap g.symm.toLinearMap
  left_inv x := by
    change
      directSumLinearMap f.symm.toLinearMap g.symm.toLinearMap
        (directSumLinearMap f.toLinearMap g.toLinearMap x) = x
    rw [← directSumLinearMap_comp_apply]
    simpa using
      directSumLinearMap_id_apply
        (m₁ := m₁) (m₂ := m₂) x
  right_inv x := by
    change
      directSumLinearMap f.toLinearMap g.toLinearMap
        (directSumLinearMap f.symm.toLinearMap g.symm.toLinearMap x) = x
    rw [← directSumLinearMap_comp_apply]
    simpa using
      directSumLinearMap_id_apply
        (m₁ := n₁) (m₂ := n₂) x

@[simp] theorem directSumLinearEquiv_apply
    {m₁ m₂ n₁ n₂ : ℕ}
    (f : (Fin m₁ → F2) ≃ₗ[F2] (Fin n₁ → F2))
    (g : (Fin m₂ → F2) ≃ₗ[F2] (Fin n₂ → F2))
    (x : Fin (m₁ + m₂) → F2) :
    directSumLinearEquiv f g x =
      Fin.append
        (f (finLeftPart x))
        (g (finRightPart x)) := rfl

/-- The left block action used on the perfect completion of a source
automorphism (f,g). -/
noncomputable def completionLeftEquiv
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (Fin (l + r) → F2) ≃ₗ[F2] (Fin (l + r) → F2) :=
  directSumLinearEquiv f (dotContragredient g)

/-- The perfect-pair automorphism induced by the canonical completion
action on the left sort. -/
noncomputable def completionAutomorphism
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    BananaMatrixEmbedding
      (perfectBanana (l + r))
      (perfectBanana (l + r)) :=
  perfectPairAutomorphismOfLinearEquiv
    (completionLeftEquiv f g)

/-- The completion automorphism extends f on the embedded left sort. -/
theorem completionAutomorphism_left_completion
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (x : Fin l → F2) :
    (completionAutomorphism f g).left (A.completionLeft x) =
      A.completionLeft (f x) := by
  change
    completionLeftEquiv f g (Fin.append x 0) =
      Fin.append (f x) 0
  apply funext
  intro i
  induction i using Fin.addCases <;>
    simp [completionLeftEquiv, directSumLinearEquiv,
      directSumLinearMap, finLeftPart, finRightPart]

/-- If f and g preserve the source pairing, the completion automorphism also
extends g on the embedded right sort. -/
theorem completionAutomorphism_right_completion
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (hpair : ∀ x y, A.eval (f x) (g y) = A.eval x y)
    (y : Fin r → F2) :
    (completionAutomorphism f g).right (A.completionRight y) =
      A.completionRight (g y) := by
  let h := completionLeftEquiv f g
  change
    dotContragredient h (A.completionRight y) =
      A.completionRight (g y)
  apply dotProduct_eq
  intro z
  obtain ⟨w, rfl⟩ := h.surjective z
  rw [dotProduct_comm
      (dotContragredient h (A.completionRight y)) (h w)]
  rw [dotContragredient_pairing]
  rw [dotProduct_comm
      (A.completionRight (g y)) (h w)]
  change
    w ⬝ᵥ A.completionRight y =
      h w ⬝ᵥ A.completionRight (g y)
  rw [show
      w =
        Fin.append (finLeftPart w) (finRightPart w) by
        funext i
        induction i using Fin.addCases <;>
          simp [finLeftPart, finRightPart]]
  rw [show
      h (Fin.append (finLeftPart w) (finRightPart w)) =
        Fin.append
          (f (finLeftPart w))
          (dotContragredient g (finRightPart w)) by
        rfl]
  unfold completionRight
  simp only [dotProduct]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  have hfg :
      (f (finLeftPart w)) ⬝ᵥ
          (A.pairing *ᵥ (g y)) =
        finLeftPart w ⬝ᵥ (A.pairing *ᵥ y) := by
    simpa [BananaMatrixStructure.eval] using
      hpair (finLeftPart w) y
  have hdual :
      dotContragredient g (finRightPart w) ⬝ᵥ g y =
        finRightPart w ⬝ᵥ y := by
    rw [dotProduct_comm
      (dotContragredient g (finRightPart w)) (g y)]
    rw [dotProduct_comm
      (finRightPart w) y]
    simpa using
      dotContragredient_pairing g y (finRightPart w)
  rw [hfg, hdual]

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
