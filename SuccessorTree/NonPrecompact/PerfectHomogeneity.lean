import SuccessorTree.NonPrecompact.BananaStructure
import SuccessorTree.NonPrecompact.LinearExtension
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Homogeneity of finite perfect BANANA pairings

This file formalises the circulation lemma saying that every isomorphism
between finite substructures of a finite perfect pairing extends to an
automorphism.  In standard coordinates, an isomorphism between two
substructures is represented by two embeddings of the same finite BANANA
structure into `B_n`.

The proof follows the manuscript.  The right-hand copy determines a
surjective map from the ambient left space to the dual of the source right
space.  The already formalised compatible-extension lemma extends the
left-hand partial isomorphism while intertwining these quotient maps.  The
right-hand automorphism is then the contragredient of the left-hand one.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix
open LinearMap Module

/-- The standard dot product identifies a finite coordinate space with its
linear dual. -/
noncomputable abbrev dotDualEquiv (n : ℕ) :
    (Fin n → F2) ≃ₗ[F2] Module.Dual F2 (Fin n → F2) :=
  Matrix.dotProductEquiv F2 (Fin n)

/-- For an embedding into a standard perfect pair, record all pairings of an
ambient left vector with the embedded right sort. -/
noncomputable def rightPairingMap
    {l r n : ℕ}
    {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbedding A (perfectBanana n)) :
    (Fin n → F2) →ₗ[F2] (Fin r → F2) :=
  (dotDualEquiv r).symm.toLinearMap.comp
    (e.right.dualMap.comp (dotDualEquiv n).toLinearMap)

@[simp] theorem rightPairingMap_pairing
    {l r n : ℕ}
    {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbedding A (perfectBanana n))
    (x : Fin n → F2) (y : Fin r → F2) :
    e.right y ⬝ᵥ x = rightPairingMap e x ⬝ᵥ y := by
  change
    (dotDualEquiv n x) (e.right y) =
      (dotDualEquiv r (rightPairingMap e x)) y
  simp [rightPairingMap, dotDualEquiv]

theorem rightPairingMap_surjective
    {l r n : ℕ}
    {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbedding A (perfectBanana n)) :
    Function.Surjective (rightPairingMap e) := by
  intro z
  let ψ : Module.Dual F2 (Fin r → F2) := dotDualEquiv r z
  obtain ⟨φ, hφ⟩ :=
    (LinearMap.dualMap_surjective_iff.mpr e.right_injective) ψ
  let x : Fin n → F2 := (dotDualEquiv n).symm φ
  refine ⟨x, ?_⟩
  apply (dotDualEquiv r).injective
  change
    dotDualEquiv r (rightPairingMap e x) = dotDualEquiv r z
  simpa [rightPairingMap, x, ψ] using hφ

namespace BananaMatrixEmbedding

variable {l r n : ℕ}
variable {A : BananaMatrixStructure l r}

/-- The source left sort is linearly equivalent to its image under an
embedding. -/
noncomputable def leftRangeEquiv
    (e : BananaMatrixEmbedding A (perfectBanana n)) :
    (Fin l → F2) ≃ₗ[F2] LinearMap.range e.left :=
  LinearEquiv.ofInjective e.left e.left_injective

end BananaMatrixEmbedding

/-- A linear automorphism and its contragredient, packaged as an automorphism
of the standard perfect BANANA pair. -/
noncomputable def perfectPairAutomorphismOfLinearEquiv
    {n : ℕ}
    (h : (Fin n → F2) ≃ₗ[F2] (Fin n → F2)) :
    BananaMatrixEmbedding (perfectBanana n) (perfectBanana n) where
  left := h.toLinearMap
  right :=
    ((dotDualEquiv n).trans h.symm.dualMap).trans
      (dotDualEquiv n).symm |>.toLinearMap
  left_injective := h.injective
  right_injective := by
    exact (((dotDualEquiv n).trans h.symm.dualMap).trans
      (dotDualEquiv n).symm).injective
  pairing_apply := by
    intro x y
    simp only [perfectBanana_eval]
    change
      h x ⬝ᵥ
          (((dotDualEquiv n).trans h.symm.dualMap).trans
            (dotDualEquiv n).symm) y =
        x ⬝ᵥ y
    change
      (dotDualEquiv n
        ((((dotDualEquiv n).trans h.symm.dualMap).trans
          (dotDualEquiv n).symm) y)) (h x) =
        x ⬝ᵥ y
    simp [dotDualEquiv, dotProduct_comm]

@[simp] theorem perfectPairAutomorphismOfLinearEquiv_left
    {n : ℕ}
    (h : (Fin n → F2) ≃ₗ[F2] (Fin n → F2))
    (x : Fin n → F2) :
    (perfectPairAutomorphismOfLinearEquiv h).left x = h x := rfl

/-- The right component of the automorphism induced by `h` is its
contragredient under the dot-product identification with the dual. -/
theorem perfectPairAutomorphismOfLinearEquiv_right_pairing
    {n : ℕ}
    (h : (Fin n → F2) ≃ₗ[F2] (Fin n → F2))
    (x y : Fin n → F2) :
    h x ⬝ᵥ
        (perfectPairAutomorphismOfLinearEquiv h).right y =
      x ⬝ᵥ y := by
  simpa only [perfectBanana_eval] using
    (perfectPairAutomorphismOfLinearEquiv h).pairing_apply x y

/-- Coordinate form of the manuscript's perfect-pair homogeneity lemma.

Given two embeddings of the same finite BANANA structure into `B_n`, there
is an automorphism of `B_n` carrying the first copy to the second on both
sorts. -/
theorem exists_perfectPairAutomorphism_extends
    {l r n : ℕ}
    {A : BananaMatrixStructure l r}
    (e₁ e₂ : BananaMatrixEmbedding A (perfectBanana n)) :
    ∃ H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n),
      (∀ x, H.left (e₁.left x) = e₂.left x) ∧
      (∀ y, H.right (e₁.right y) = e₂.right y) := by
  let A₁ : Submodule F2 (Fin n → F2) := LinearMap.range e₁.left
  let A₂ : Submodule F2 (Fin n → F2) := LinearMap.range e₂.left
  let u₁ : (Fin l → F2) ≃ₗ[F2] A₁ := e₁.leftRangeEquiv
  let u₂ : (Fin l → F2) ≃ₗ[F2] A₂ := e₂.leftRangeEquiv
  let f : A₁ ≃ₗ[F2] A₂ := u₁.symm ≪≫ₗ u₂
  let q₁ := rightPairingMap e₁
  let q₂ := rightPairingMap e₂

  have hf (z : A₁) : q₂ (f z) = q₁ z := by
    apply dotProduct_eq
    intro y
    rw [← rightPairingMap_pairing e₂ (f z) y,
      ← rightPairingMap_pairing e₁ z y]
    let x : Fin l → F2 := u₁.symm z
    have hz₁ : (z : Fin n → F2) = e₁.left x := by
      change (u₁ x : Fin n → F2) = e₁.left x
      rfl
    have hzf : (f z : Fin n → F2) = e₂.left x := by
      change (u₂ x : Fin n → F2) = e₂.left x
      rfl
    rw [hz₁, hzf]
    rw [dotProduct_comm (e₂.right y), dotProduct_comm (e₁.right y)]
    simpa only [perfectBanana_eval] using
      (e₂.pairing_apply x y).trans (e₁.pairing_apply x y).symm

  obtain ⟨h, hleftRange, hq⟩ :=
    exists_linearEquiv_extends_of_surjective
      q₁ q₂
      (rightPairingMap_surjective e₁)
      (rightPairingMap_surjective e₂)
      f hf

  let H := perfectPairAutomorphismOfLinearEquiv h

  have hleft (x : Fin l → F2) :
      H.left (e₁.left x) = e₂.left x := by
    let z : A₁ := u₁ x
    have hz := hleftRange z
    change h (e₁.left x) = e₂.left x
    simpa [H, f, z, u₁, u₂] using hz

  have hright (y : Fin r → F2) :
      H.right (e₁.right y) = e₂.right y := by
    apply dotProduct_eq
    intro w
    obtain ⟨x, rfl⟩ := h.surjective w
    rw [← dotProduct_comm]
    rw [H.perfectPairAutomorphismOfLinearEquiv_right_pairing]
    rw [dotProduct_comm]
    have hqy := LinearMap.congr_fun hq x
    have hpair₁ :=
      rightPairingMap_pairing e₁ x y
    have hpair₂ :=
      rightPairingMap_pairing e₂ (h x) y
    rw [hqy] at hpair₂
    exact hpair₁.trans hpair₂.symm

  exact ⟨H, hleft, hright⟩

end SuccessorTree.NonPrecompact
