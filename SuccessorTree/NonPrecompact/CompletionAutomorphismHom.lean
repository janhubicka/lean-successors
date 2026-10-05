import SuccessorTree.NonPrecompact.CompletionAutomorphism

/-!
# Homomorphism law for the perfect-completion action

The BANANA coherent-EPPA proof uses the canonical action

  (f,g) ↦ f ⊕ (g⁻¹)^*

on the left side of the perfect completion, with the corresponding
contragredient action on the right.  This file proves that the construction
preserves identities and composition on both sorts.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- The dot-product contragredient of the identity is the identity. -/
theorem dotContragredient_refl
    {n : ℕ} :
    dotContragredient
        (LinearEquiv.refl F2 (Fin n → F2)) =
      LinearEquiv.refl F2 (Fin n → F2) := by
  apply LinearEquiv.ext
  intro y
  apply dotProduct_eq
  intro x
  calc
    dotContragredient
          (LinearEquiv.refl F2 (Fin n → F2)) y ⬝ᵥ x =
        x ⬝ᵥ
          dotContragredient
            (LinearEquiv.refl F2 (Fin n → F2)) y := by
          rw [dotProduct_comm]
    _ = x ⬝ᵥ y := by
      simpa using
        dotContragredient_pairing
          (LinearEquiv.refl F2 (Fin n → F2)) x y
    _ = y ⬝ᵥ x := by
      rw [dotProduct_comm]

/-- Contragredients preserve composition in the same order as linear
equivalences. -/
theorem dotContragredient_trans
    {n : ℕ}
    (f g : (Fin n → F2) ≃ₗ[F2] (Fin n → F2)) :
    dotContragredient (f.trans g) =
      (dotContragredient f).trans (dotContragredient g) := by
  apply LinearEquiv.ext
  intro y
  apply dotProduct_eq
  intro z
  obtain ⟨x, rfl⟩ := (f.trans g).surjective z
  calc
    dotContragredient (f.trans g) y ⬝ᵥ (f.trans g) x =
        (f.trans g) x ⬝ᵥ dotContragredient (f.trans g) y := by
          rw [dotProduct_comm]
    _ = x ⬝ᵥ y := by
      exact dotContragredient_pairing (f.trans g) x y
    _ = f x ⬝ᵥ dotContragredient f y := by
      exact (dotContragredient_pairing f x y).symm
    _ = g (f x) ⬝ᵥ
          dotContragredient g (dotContragredient f y) := by
      exact
        (dotContragredient_pairing
          g (f x) (dotContragredient f y)).symm
    _ = ((dotContragredient f).trans (dotContragredient g)) y ⬝ᵥ
          (f.trans g) x := by
      rw [dotProduct_comm]
      rfl

/-- Direct sums of linear equivalences preserve identities. -/
theorem directSumLinearEquiv_refl
    {m n : ℕ} :
    directSumLinearEquiv
        (LinearEquiv.refl F2 (Fin m → F2))
        (LinearEquiv.refl F2 (Fin n → F2)) =
      LinearEquiv.refl F2 (Fin (m + n) → F2) := by
  apply LinearEquiv.ext
  intro x
  change
    directSumLinearMap
        (LinearMap.id : (Fin m → F2) →ₗ[F2] (Fin m → F2))
        (LinearMap.id : (Fin n → F2) →ₗ[F2] (Fin n → F2)) x =
      x
  exact directSumLinearMap_id_apply x

/-- Direct sums of linear equivalences preserve composition. -/
theorem directSumLinearEquiv_trans
    {m₁ m₂ n₁ n₂ p₁ p₂ : ℕ}
    (f₁ : (Fin m₁ → F2) ≃ₗ[F2] (Fin n₁ → F2))
    (f₂ : (Fin n₁ → F2) ≃ₗ[F2] (Fin p₁ → F2))
    (g₁ : (Fin m₂ → F2) ≃ₗ[F2] (Fin n₂ → F2))
    (g₂ : (Fin n₂ → F2) ≃ₗ[F2] (Fin p₂ → F2)) :
    directSumLinearEquiv (f₁.trans f₂) (g₁.trans g₂) =
      (directSumLinearEquiv f₁ g₁).trans
        (directSumLinearEquiv f₂ g₂) := by
  apply LinearEquiv.ext
  intro x
  change
    Fin.append
        (f₂ (f₁ (finLeftPart x)))
        (g₂ (g₁ (finRightPart x))) =
      directSumLinearEquiv f₂ g₂
        (directSumLinearEquiv f₁ g₁ x)
  rw [directSumLinearEquiv_apply, directSumLinearEquiv_apply]
  simp

/-- The left completion action preserves the identity. -/
theorem completionLeftEquiv_refl
    {l r : ℕ} :
    completionLeftEquiv
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2)) =
      LinearEquiv.refl F2 (Fin (l + r) → F2) := by
  unfold completionLeftEquiv
  rw [dotContragredient_refl]
  exact directSumLinearEquiv_refl

/-- The left completion action preserves composition. -/
theorem completionLeftEquiv_trans
    {l r : ℕ}
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    completionLeftEquiv (f₁.trans f₂) (g₁.trans g₂) =
      (completionLeftEquiv f₁ g₁).trans
        (completionLeftEquiv f₂ g₂) := by
  unfold completionLeftEquiv
  rw [dotContragredient_trans]
  exact directSumLinearEquiv_trans f₁ f₂
    (dotContragredient g₁) (dotContragredient g₂)

/-- The left component of the perfect-completion automorphism preserves
composition. -/
theorem completionAutomorphism_comp_left
    {l r : ℕ}
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (completionAutomorphism (f₁.trans f₂) (g₁.trans g₂)).left =
      (BananaMatrixEmbedding.comp
        (completionAutomorphism f₂ g₂)
        (completionAutomorphism f₁ g₁)).left := by
  apply LinearMap.ext
  intro x
  change
    completionLeftEquiv (f₁.trans f₂) (g₁.trans g₂) x =
      completionLeftEquiv f₂ g₂
        (completionLeftEquiv f₁ g₁ x)
  have h :=
    congrArg
      (fun h :
        (Fin (l + r) → F2) ≃ₗ[F2] (Fin (l + r) → F2) => h x)
      (completionLeftEquiv_trans f₁ f₂ g₁ g₂)
  exact h

/-- The right component of the perfect-completion automorphism preserves
composition. -/
theorem completionAutomorphism_comp_right
    {l r : ℕ}
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (completionAutomorphism (f₁.trans f₂) (g₁.trans g₂)).right =
      (BananaMatrixEmbedding.comp
        (completionAutomorphism f₂ g₂)
        (completionAutomorphism f₁ g₁)).right := by
  apply LinearMap.ext
  intro y
  change
    dotContragredient
        (completionLeftEquiv (f₁.trans f₂) (g₁.trans g₂)) y =
      dotContragredient (completionLeftEquiv f₂ g₂)
        (dotContragredient (completionLeftEquiv f₁ g₁) y)
  rw [completionLeftEquiv_trans, dotContragredient_trans]
  rfl

/-- The left component of the perfect-completion action sends the identity
source automorphism to the identity. -/
theorem completionAutomorphism_refl_left
    {l r : ℕ} :
    (completionAutomorphism
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2))).left =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  change
    completionLeftEquiv
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2)) x = x
  rw [completionLeftEquiv_refl]
  rfl

/-- The right component of the perfect-completion action sends the identity
source automorphism to the identity. -/
theorem completionAutomorphism_refl_right
    {l r : ℕ} :
    (completionAutomorphism
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2))).right =
      LinearMap.id := by
  apply LinearMap.ext
  intro y
  change
    dotContragredient
      (completionLeftEquiv
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2))) y = y
  rw [completionLeftEquiv_refl, dotContragredient_refl]
  rfl

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
