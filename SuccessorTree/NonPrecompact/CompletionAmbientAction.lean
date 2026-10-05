import SuccessorTree.NonPrecompact.CompletionAutomorphismHom

/-!
# Ambient extension of the perfect-completion action

In the coherent-EPPA proof, an embedded perfect completion splits off
orthogonally inside the ambient perfect witness and its automorphism action
is extended by the identity on the perfect complement.

This file formalises the standard-coordinate version of that construction:
the completion is the first block of a larger standard perfect pairing and
the second block is fixed pointwise.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- The contragredient of a block-diagonal linear equivalence is the
block-diagonal direct sum of the two contragredients. -/
theorem dotContragredient_directSumLinearEquiv
    {m n : ℕ}
    (f : (Fin m → F2) ≃ₗ[F2] (Fin m → F2))
    (g : (Fin n → F2) ≃ₗ[F2] (Fin n → F2)) :
    dotContragredient (directSumLinearEquiv f g) =
      directSumLinearEquiv
        (dotContragredient f) (dotContragredient g) := by
  apply LinearEquiv.ext
  intro y
  apply dotProduct_eq
  intro z
  obtain ⟨x, rfl⟩ := (directSumLinearEquiv f g).surjective z
  have hx :
      x = Fin.append (finLeftPart x) (finRightPart x) := by
    funext i
    induction i using Fin.addCases <;>
      simp [finLeftPart, finRightPart]
  have hy :
      y = Fin.append (finLeftPart y) (finRightPart y) := by
    funext i
    induction i using Fin.addCases <;>
      simp [finLeftPart, finRightPart]
  calc
    dotContragredient (directSumLinearEquiv f g) y ⬝ᵥ
        directSumLinearEquiv f g x =
      directSumLinearEquiv f g x ⬝ᵥ
        dotContragredient (directSumLinearEquiv f g) y := by
          rw [dotProduct_comm]
    _ = x ⬝ᵥ y := by
      exact
        dotContragredient_pairing
          (directSumLinearEquiv f g) x y
    _ =
        (finLeftPart x ⬝ᵥ finLeftPart y) +
          (finRightPart x ⬝ᵥ finRightPart y) := by
      rw [hx, hy, dotProduct_append]
    _ =
        (f (finLeftPart x) ⬝ᵥ
          dotContragredient f (finLeftPart y)) +
        (g (finRightPart x) ⬝ᵥ
          dotContragredient g (finRightPart y)) := by
      rw [dotContragredient_pairing f,
        dotContragredient_pairing g]
    _ =
        directSumLinearEquiv f g x ⬝ᵥ
          directSumLinearEquiv
            (dotContragredient f)
            (dotContragredient g) y := by
      rw [directSumLinearEquiv_apply,
        directSumLinearEquiv_apply]
      exact
        (dotProduct_append
          (f (finLeftPart x))
          (dotContragredient f (finLeftPart y))
          (g (finRightPart x))
          (dotContragredient g (finRightPart y))).symm
    _ =
        directSumLinearEquiv
            (dotContragredient f)
            (dotContragredient g) y ⬝ᵥ
          directSumLinearEquiv f g x := by
      rw [dotProduct_comm]

/-- Left action on an ambient perfect pairing obtained by adjoining a perfect
complement on which the completion action is the identity. -/
noncomputable def completionAmbientLeftEquiv
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ) :
    (Fin ((l + r) + k) → F2) ≃ₗ[F2]
      (Fin ((l + r) + k) → F2) :=
  directSumLinearEquiv
    (completionLeftEquiv f g)
    (LinearEquiv.refl F2 (Fin k → F2))

/-- The corresponding automorphism of the ambient standard perfect pairing. -/
noncomputable def completionAmbientAutomorphism
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ) :
    BananaMatrixEmbedding
      (perfectBanana ((l + r) + k))
      (perfectBanana ((l + r) + k)) :=
  perfectPairAutomorphismOfLinearEquiv
    (completionAmbientLeftEquiv f g k)

/-- On the first block, the ambient action extends the original left
automorphism of the source structure. -/
theorem completionAmbientAutomorphism_left_completion
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ)
    (x : Fin l → F2) :
    (completionAmbientAutomorphism f g k).left
        (Fin.append (A.completionLeft x) 0) =
      Fin.append (A.completionLeft (f x)) 0 := by
  change
    completionAmbientLeftEquiv f g k
        (Fin.append (A.completionLeft x) 0) =
      Fin.append (A.completionLeft (f x)) 0
  rw [completionAmbientLeftEquiv, directSumLinearEquiv_apply]
  simp only [finLeftPart_append, finRightPart_append,
    LinearEquiv.refl_apply]
  have h :=
    completionAutomorphism_left_completion A f g x
  exact congrArg (fun z => Fin.append z (0 : Fin k → F2)) h

/-- On the first block, the ambient action extends the original right
automorphism whenever the source pair is preserved. -/
theorem completionAmbientAutomorphism_right_completion
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (hpair : ∀ x y, A.eval (f x) (g y) = A.eval x y)
    (k : ℕ)
    (y : Fin r → F2) :
    (completionAmbientAutomorphism f g k).right
        (Fin.append (A.completionRight y) 0) =
      Fin.append (A.completionRight (g y)) 0 := by
  change
    dotContragredient (completionAmbientLeftEquiv f g k)
        (Fin.append (A.completionRight y) 0) =
      Fin.append (A.completionRight (g y)) 0
  rw [completionAmbientLeftEquiv,
    dotContragredient_directSumLinearEquiv,
    dotContragredient_refl,
    directSumLinearEquiv_apply]
  simp only [finLeftPart_append, finRightPart_append,
    LinearEquiv.refl_apply]
  have h :=
    completionAutomorphism_right_completion A f g hpair y
  exact congrArg (fun z => Fin.append z (0 : Fin k → F2)) h

/-- The adjoining perfect complement is fixed pointwise on the left sort. -/
theorem completionAmbientAutomorphism_left_complement
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ)
    (z : Fin k → F2) :
    (completionAmbientAutomorphism f g k).left
        (Fin.append 0 z) =
      Fin.append 0 z := by
  change
    completionAmbientLeftEquiv f g k (Fin.append 0 z) =
      Fin.append 0 z
  rw [completionAmbientLeftEquiv, directSumLinearEquiv_apply]
  simp

/-- The adjoining perfect complement is fixed pointwise on the right sort. -/
theorem completionAmbientAutomorphism_right_complement
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ)
    (z : Fin k → F2) :
    (completionAmbientAutomorphism f g k).right
        (Fin.append 0 z) =
      Fin.append 0 z := by
  change
    dotContragredient (completionAmbientLeftEquiv f g k)
        (Fin.append 0 z) =
      Fin.append 0 z
  rw [completionAmbientLeftEquiv,
    dotContragredient_directSumLinearEquiv,
    dotContragredient_refl,
    directSumLinearEquiv_apply]
  simp

/-- The ambient left action preserves composition. -/
theorem completionAmbientAutomorphism_comp_left
    {l r : ℕ}
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ) :
    (completionAmbientAutomorphism
      (f₁.trans f₂) (g₁.trans g₂) k).left =
      (BananaMatrixEmbedding.comp
        (completionAmbientAutomorphism f₂ g₂ k)
        (completionAmbientAutomorphism f₁ g₁ k)).left := by
  apply LinearMap.ext
  intro x
  change
    completionAmbientLeftEquiv
        (f₁.trans f₂) (g₁.trans g₂) k x =
      completionAmbientLeftEquiv f₂ g₂ k
        (completionAmbientLeftEquiv f₁ g₁ k x)
  unfold completionAmbientLeftEquiv
  rw [completionLeftEquiv_trans]
  simpa using
    congrArg
      (fun h :
        (Fin ((l + r) + k) → F2) ≃ₗ[F2]
          (Fin ((l + r) + k) → F2) => h x)
      (directSumLinearEquiv_trans
        (completionLeftEquiv f₁ g₁)
        (completionLeftEquiv f₂ g₂)
        (LinearEquiv.refl F2 (Fin k → F2))
        (LinearEquiv.refl F2 (Fin k → F2)))

/-- The ambient right action preserves composition. -/
theorem completionAmbientAutomorphism_comp_right
    {l r : ℕ}
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ) :
    (completionAmbientAutomorphism
      (f₁.trans f₂) (g₁.trans g₂) k).right =
      (BananaMatrixEmbedding.comp
        (completionAmbientAutomorphism f₂ g₂ k)
        (completionAmbientAutomorphism f₁ g₁ k)).right := by
  apply LinearMap.ext
  intro y
  change
    dotContragredient
        (completionAmbientLeftEquiv
          (f₁.trans f₂) (g₁.trans g₂) k) y =
      dotContragredient
        (completionAmbientLeftEquiv f₂ g₂ k)
        (dotContragredient
          (completionAmbientLeftEquiv f₁ g₁ k) y)
  have hleft :
      completionAmbientLeftEquiv
          (f₁.trans f₂) (g₁.trans g₂) k =
        (completionAmbientLeftEquiv f₁ g₁ k).trans
          (completionAmbientLeftEquiv f₂ g₂ k) := by
    unfold completionAmbientLeftEquiv
    rw [completionLeftEquiv_trans]
    exact directSumLinearEquiv_trans
      (completionLeftEquiv f₁ g₁)
      (completionLeftEquiv f₂ g₂)
      (LinearEquiv.refl F2 (Fin k → F2))
      (LinearEquiv.refl F2 (Fin k → F2))
  rw [hleft, dotContragredient_trans]
  rfl

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
