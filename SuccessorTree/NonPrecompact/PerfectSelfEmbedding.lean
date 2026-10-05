import SuccessorTree.NonPrecompact.CompletionAutomorphismHom
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Self-embeddings of finite perfect pairings are automorphisms

A BANANA embedding from a finite standard perfect pairing to itself is
automatically bijective on each finite vector-space sort.  Its left map
therefore gives a linear equivalence, and pairing preservation forces the
right map to be the corresponding dot-product contragredient.

This is the conjugation interface needed by the coherent-EPPA construction.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixEmbedding

/-- The left component of a self-embedding of a finite standard perfect
pairing, bundled as a linear equivalence. -/
noncomputable def leftSelfEquiv
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n)) :
    (Fin n → F2) ≃ₗ[F2] (Fin n → F2) :=
  LinearEquiv.ofBijective H.left
    ⟨H.left_injective,
      Finite.injective_iff_surjective.mp H.left_injective⟩

@[simp] theorem leftSelfEquiv_apply
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (x : Fin n → F2) :
    H.leftSelfEquiv x = H.left x := rfl

/-- Pairing preservation determines the right component of a perfect
self-embedding as the contragredient of its left linear equivalence. -/
theorem right_eq_dotContragredient_leftSelfEquiv
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n)) :
    H.right =
      (dotContragredient H.leftSelfEquiv).toLinearMap := by
  apply LinearMap.ext
  intro y
  apply dotProduct_eq
  intro z
  obtain ⟨x, rfl⟩ := H.leftSelfEquiv.surjective z
  calc
    H.right y ⬝ᵥ H.leftSelfEquiv x =
        H.leftSelfEquiv x ⬝ᵥ H.right y := by
          rw [dotProduct_comm]
    _ = x ⬝ᵥ y := by
      change H.left x ⬝ᵥ H.right y = x ⬝ᵥ y
      simpa only [perfectBanana_eval] using
        H.pairing_apply x y
    _ = H.leftSelfEquiv x ⬝ᵥ
          dotContragredient H.leftSelfEquiv y := by
      exact
        (dotContragredient_pairing
          H.leftSelfEquiv x y).symm
    _ = dotContragredient H.leftSelfEquiv y ⬝ᵥ
          H.leftSelfEquiv x := by
      rw [dotProduct_comm]

/-- Every perfect self-embedding is exactly the automorphism induced by its
left linear equivalence. -/
theorem eq_perfectPairAutomorphismOf_leftSelfEquiv
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n)) :
    H.left =
        (perfectPairAutomorphismOfLinearEquiv H.leftSelfEquiv).left ∧
      H.right =
        (perfectPairAutomorphismOfLinearEquiv H.leftSelfEquiv).right := by
  constructor
  · apply LinearMap.ext
    intro x
    rfl
  · exact H.right_eq_dotContragredient_leftSelfEquiv

/-- The inverse left linear equivalence induces the inverse perfect-pair
automorphism on both sorts. -/
noncomputable def inversePerfectSelfEmbedding
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n)) :
    BananaMatrixEmbedding (perfectBanana n) (perfectBanana n) :=
  perfectPairAutomorphismOfLinearEquiv H.leftSelfEquiv.symm

/-- The left component of the constructed inverse is a left inverse to H. -/
theorem inversePerfectSelfEmbedding_left_comp
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (x : Fin n → F2) :
    (inversePerfectSelfEmbedding H).left (H.left x) = x := by
  change H.leftSelfEquiv.symm (H.leftSelfEquiv x) = x
  exact H.leftSelfEquiv.symm_apply_apply x

/-- The right component of the constructed inverse is a left inverse to H. -/
theorem inversePerfectSelfEmbedding_right_comp
    {n : ℕ}
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (y : Fin n → F2) :
    (inversePerfectSelfEmbedding H).right (H.right y) = y := by
  have hright := H.right_eq_dotContragredient_leftSelfEquiv
  rw [hright]
  change
    dotContragredient H.leftSelfEquiv.symm
        (dotContragredient H.leftSelfEquiv y) = y
  have hcomp :=
    congrArg
      (fun h : (Fin n → F2) ≃ₗ[F2] (Fin n → F2) => h y)
      (dotContragredient_trans
        H.leftSelfEquiv H.leftSelfEquiv.symm)
  simpa [dotContragredient_refl] using hcomp

end BananaMatrixEmbedding

end SuccessorTree.NonPrecompact
