import SuccessorTree.NonPrecompact.CompletionAmbientAction
import SuccessorTree.NonPrecompact.PerfectBlockConjugator
import SuccessorTree.NonPrecompact.PerfectSelfEmbedding

/-!
# Conjugated ambient completion actions

This file packages the remaining finite-algebra layer of the BANANA coherent
EPPA proof.

A perfect completion embedded in a larger perfect witness is first moved to
the standard first coordinate block by an ambient perfect-pair automorphism.
The canonical completion action is extended by the identity on the remaining
perfect block, then conjugated back.

The resulting ambient action extends the chosen completion action and
preserves identities and composition.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- On the first standard block, the ambient completion action is exactly the
completion action. -/
theorem completionAmbientAutomorphism_left_block
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ)
    (z : Fin (l + r) → F2) :
    (completionAmbientAutomorphism f g k).left
        (Fin.append z 0) =
      Fin.append (completionLeftEquiv f g z) 0 := by
  change
    completionAmbientLeftEquiv f g k (Fin.append z 0) =
      Fin.append (completionLeftEquiv f g z) 0
  rw [completionAmbientLeftEquiv, directSumLinearEquiv_apply]
  simp

/-- The corresponding statement on the right standard block. -/
theorem completionAmbientAutomorphism_right_block
    {l r : ℕ}
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ)
    (z : Fin (l + r) → F2) :
    (completionAmbientAutomorphism f g k).right
        (Fin.append z 0) =
      Fin.append (dotContragredient (completionLeftEquiv f g) z) 0 := by
  change
    dotContragredient (completionAmbientLeftEquiv f g k)
        (Fin.append z 0) =
      Fin.append (dotContragredient (completionLeftEquiv f g) z) 0
  rw [completionAmbientLeftEquiv,
    dotContragredient_directSumLinearEquiv,
    dotContragredient_refl,
    directSumLinearEquiv_apply]
  simp

/-- The ambient completion action sends identity source automorphisms to the
identity on the left sort. -/
theorem completionAmbientAutomorphism_refl_left
    {l r : ℕ} (k : ℕ) :
    (completionAmbientAutomorphism
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2)) k).left =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change
    completionAmbientLeftEquiv
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2)) k z = z
  unfold completionAmbientLeftEquiv
  rw [completionLeftEquiv_refl, directSumLinearEquiv_refl]
  rfl

/-- The ambient completion action sends identity source automorphisms to the
identity on the right sort. -/
theorem completionAmbientAutomorphism_refl_right
    {l r : ℕ} (k : ℕ) :
    (completionAmbientAutomorphism
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2)) k).right =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  change
    dotContragredient
      (completionAmbientLeftEquiv
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2)) k) z = z
  have hleft :
      completionAmbientLeftEquiv
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2)) k =
      LinearEquiv.refl F2 (Fin ((l + r) + k) → F2) := by
    unfold completionAmbientLeftEquiv
    rw [completionLeftEquiv_refl, directSumLinearEquiv_refl]
  rw [hleft, dotContragredient_refl]
  rfl

end BananaMatrixStructure

namespace BananaMatrixEmbedding

/-- The constructed inverse to a perfect self-embedding is also a right
inverse on the left sort. -/
theorem inversePerfectSelfEmbedding_left_rightInverse
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (x : Fin n → F2) :
    H.left ((inversePerfectSelfEmbedding H).left x) = x := by
  change H.leftSelfEquiv (H.leftSelfEquiv.symm x) = x
  exact H.leftSelfEquiv.apply_symm_apply x

/-- The constructed inverse is a right inverse on the right sort as well. -/
theorem inversePerfectSelfEmbedding_right_rightInverse
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (y : Fin n → F2) :
    H.right ((inversePerfectSelfEmbedding H).right y) = y := by
  apply (inversePerfectSelfEmbedding H).right_injective
  rw [inversePerfectSelfEmbedding_right_comp]
  rfl

end BananaMatrixEmbedding

namespace BananaMatrixStructure

/-- Conjugate the standard ambient completion action by an arbitrary
perfect-pair automorphism of the ambient witness. -/
noncomputable def conjugatedCompletionAmbientAutomorphism
    {l r : ℕ}
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k)))
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (k : ℕ) :
    BananaMatrixEmbedding
      (perfectBanana ((l + r) + k))
      (perfectBanana ((l + r) + k)) :=
  BananaMatrixEmbedding.comp H
    (BananaMatrixEmbedding.comp
      (completionAmbientAutomorphism f g k)
      (BananaMatrixEmbedding.inversePerfectSelfEmbedding H))

/-- After conjugating a standard perfect block onto an embedded completion,
the ambient action restricts to the completion action on the embedded left
block. -/
theorem conjugatedCompletionAmbientAutomorphism_left_embedded
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k)))
    (hH :
      ∀ z : Fin (l + r) → F2,
        H.left (Fin.append z 0) = E.left z)
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (z : Fin (l + r) → F2) :
    (conjugatedCompletionAmbientAutomorphism H f g k).left
        (E.left z) =
      E.left (completionLeftEquiv f g z) := by
  change
    H.left
      ((completionAmbientAutomorphism f g k).left
        ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).left
          (E.left z))) =
      E.left (completionLeftEquiv f g z)
  rw [← hH z,
    BananaMatrixEmbedding.inversePerfectSelfEmbedding_left_comp,
    completionAmbientAutomorphism_left_block,
    hH]

/-- The corresponding restriction statement on the embedded right block. -/
theorem conjugatedCompletionAmbientAutomorphism_right_embedded
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k)))
    (hH :
      ∀ z : Fin (l + r) → F2,
        H.right (Fin.append z 0) = E.right z)
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (z : Fin (l + r) → F2) :
    (conjugatedCompletionAmbientAutomorphism H f g k).right
        (E.right z) =
      E.right
        (dotContragredient (completionLeftEquiv f g) z) := by
  change
    H.right
      ((completionAmbientAutomorphism f g k).right
        ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).right
          (E.right z))) =
      E.right
        (dotContragredient (completionLeftEquiv f g) z)
  rw [← hH z,
    BananaMatrixEmbedding.inversePerfectSelfEmbedding_right_comp,
    completionAmbientAutomorphism_right_block,
    hH]

/-- The conjugated ambient action sends identity source automorphisms to the
identity on the left sort. -/
theorem conjugatedCompletionAmbientAutomorphism_refl_left
    {l r k : ℕ}
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k))) :
    (conjugatedCompletionAmbientAutomorphism H
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2)) k).left =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  change
    H.left
      ((completionAmbientAutomorphism
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2)) k).left
        ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).left x)) =
      x
  rw [completionAmbientAutomorphism_refl_left]
  exact
    BananaMatrixEmbedding.inversePerfectSelfEmbedding_left_rightInverse
      H x

/-- Identity law on the right sort. -/
theorem conjugatedCompletionAmbientAutomorphism_refl_right
    {l r k : ℕ}
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k))) :
    (conjugatedCompletionAmbientAutomorphism H
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2)) k).right =
      LinearMap.id := by
  apply LinearMap.ext
  intro y
  change
    H.right
      ((completionAmbientAutomorphism
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2)) k).right
        ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).right y)) =
      y
  rw [completionAmbientAutomorphism_refl_right]
  exact
    BananaMatrixEmbedding.inversePerfectSelfEmbedding_right_rightInverse
      H y

/-- Composition law for the conjugated ambient action on the left sort. -/
theorem conjugatedCompletionAmbientAutomorphism_comp_left
    {l r k : ℕ}
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k)))
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (conjugatedCompletionAmbientAutomorphism H
      (f₁.trans f₂) (g₁.trans g₂) k).left =
      (BananaMatrixEmbedding.comp
        (conjugatedCompletionAmbientAutomorphism H f₂ g₂ k)
        (conjugatedCompletionAmbientAutomorphism H f₁ g₁ k)).left := by
  apply LinearMap.ext
  intro x
  change
    H.left
      ((completionAmbientAutomorphism
        (f₁.trans f₂) (g₁.trans g₂) k).left
        ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).left x)) =
      H.left
        ((completionAmbientAutomorphism f₂ g₂ k).left
          ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).left
            (H.left
              ((completionAmbientAutomorphism f₁ g₁ k).left
                ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).left
                  x)))))
  rw [BananaMatrixEmbedding.inversePerfectSelfEmbedding_left_comp]
  have hstd :=
    congrArg
      (fun L : (Fin ((l + r) + k) → F2) →ₗ[F2]
        (Fin ((l + r) + k) → F2) =>
        L ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).left x))
      (completionAmbientAutomorphism_comp_left f₁ f₂ g₁ g₂ k)
  exact congrArg H.left hstd

/-- Composition law for the conjugated ambient action on the right sort. -/
theorem conjugatedCompletionAmbientAutomorphism_comp_right
    {l r k : ℕ}
    (H :
      BananaMatrixEmbedding
        (perfectBanana ((l + r) + k))
        (perfectBanana ((l + r) + k)))
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (conjugatedCompletionAmbientAutomorphism H
      (f₁.trans f₂) (g₁.trans g₂) k).right =
      (BananaMatrixEmbedding.comp
        (conjugatedCompletionAmbientAutomorphism H f₂ g₂ k)
        (conjugatedCompletionAmbientAutomorphism H f₁ g₁ k)).right := by
  apply LinearMap.ext
  intro y
  change
    H.right
      ((completionAmbientAutomorphism
        (f₁.trans f₂) (g₁.trans g₂) k).right
        ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).right y)) =
      H.right
        ((completionAmbientAutomorphism f₂ g₂ k).right
          ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).right
            (H.right
              ((completionAmbientAutomorphism f₁ g₁ k).right
                ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).right
                  y)))))
  rw [BananaMatrixEmbedding.inversePerfectSelfEmbedding_right_comp]
  have hstd :=
    congrArg
      (fun L : (Fin ((l + r) + k) → F2) →ₗ[F2]
        (Fin ((l + r) + k) → F2) =>
        L ((BananaMatrixEmbedding.inversePerfectSelfEmbedding H).right y))
      (completionAmbientAutomorphism_comp_right f₁ f₂ g₁ g₂ k)
  exact congrArg H.right hstd

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
