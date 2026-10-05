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


@[simp] theorem finLeftPart_append
    {m n : ℕ} (x : Fin m → F2) (y : Fin n → F2) :
    finLeftPart (Fin.append x y) = x := by
  funext i
  simp [finLeftPart]

@[simp] theorem finRightPart_append
    {m n : ℕ} (x : Fin m → F2) (y : Fin n → F2) :
    finRightPart (Fin.append x y) = y := by
  funext i
  simp [finRightPart]

theorem dotProduct_append
    {m n : ℕ}
    (x₁ y₁ : Fin m → F2)
    (x₂ y₂ : Fin n → F2) :
    Fin.append x₁ x₂ ⬝ᵥ Fin.append y₁ y₂ =
      (x₁ ⬝ᵥ y₁) + (x₂ ⬝ᵥ y₂) := by
  unfold dotProduct
  rw [Fin.sum_univ_add]
  simp

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
  rw [completionLeftEquiv, directSumLinearEquiv_apply]
  simp

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
  calc
    dotContragredient h (A.completionRight y) ⬝ᵥ h w =
        h w ⬝ᵥ dotContragredient h (A.completionRight y) := by
          rw [dotProduct_comm]
    _ = w ⬝ᵥ A.completionRight y := by
          exact dotContragredient_pairing h w (A.completionRight y)
    _ = h w ⬝ᵥ A.completionRight (g y) := by
      have hw :
          w = Fin.append (finLeftPart w) (finRightPart w) := by
        funext i
        induction i using Fin.addCases <;>
          simp [finLeftPart, finRightPart]
      have hhw :
          h w =
            Fin.append
              (f (finLeftPart w))
              (dotContragredient g (finRightPart w)) := by
        rw [hw]
        simp [h, completionLeftEquiv]
      rw [hw]
      have hhw' :
          h (Fin.append (finLeftPart w) (finRightPart w)) =
            Fin.append
              (f (finLeftPart w))
              (dotContragredient g (finRightPart w)) := by
        simpa [← hw] using hhw
      rw [hhw']
      unfold completionRight
      rw [dotProduct_append, dotProduct_append]
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
    _ = A.completionRight (g y) ⬝ᵥ h w := by
      rw [dotProduct_comm]

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
