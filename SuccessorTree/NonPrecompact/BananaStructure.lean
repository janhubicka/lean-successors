import SuccessorTree.NonPrecompact.PerfectCopy

/-!
# Coordinate BANANA structures and embeddings

This file packages the finite two-sorted bilinear structures used in the
BANANA manuscript.  The two sorts are coordinate vector spaces over `F₂`;
a structure is given by the matrix of its cross-pairing, and an embedding is
a pair of injective linear maps preserving that pairing.

The main bridge shows that `PerfectCopyMatrices` really is the matrix
presentation of an embedding between the standard perfect pairings.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- A finite coordinate presentation of a BANANA structure:
two finite-dimensional `F₂` vector spaces and a bilinear cross-pairing. -/
structure CoordinateBanana (l r : ℕ) where
  pairingMatrix : Matrix (Fin l) (Fin r) F2

namespace CoordinateBanana

variable {l r l' r' l'' r'' : ℕ}

/-- Evaluation of the cross-pairing. -/
noncomputable def pair (A : CoordinateBanana l r)
    (x : Fin l → F2) (y : Fin r → F2) : F2 :=
  x ⬝ᵥ (A.pairingMatrix *ᵥ y)

/-- The standard perfect pairing `B_d`. -/
def perfect (d : ℕ) : CoordinateBanana d d where
  pairingMatrix := 1

@[simp] theorem perfect_pair (d : ℕ)
    (x y : Fin d → F2) :
    (perfect d).pair x y = x ⬝ᵥ y := by
  simp [pair, perfect]

/-- An embedding of finite BANANA structures is a pair of injective linear
maps, one on each sort, preserving the cross-pairing. -/
structure Embedding
    (A : CoordinateBanana l r) (B : CoordinateBanana l' r') where
  left : (Fin l → F2) →ₗ[F2] (Fin l' → F2)
  right : (Fin r → F2) →ₗ[F2] (Fin r' → F2)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  pairing_apply :
    ∀ x y, B.pair (left x) (right y) = A.pair x y

namespace Embedding

variable {A : CoordinateBanana l r}
  {B : CoordinateBanana l' r'}
  {C : CoordinateBanana l'' r''}

/-- Identity embedding. -/
def refl (A : CoordinateBanana l r) : Embedding A A where
  left := LinearMap.id
  right := LinearMap.id
  left_injective := Function.injective_id
  right_injective := Function.injective_id
  pairing_apply := by simp

/-- Composition of BANANA embeddings. -/
def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  left := g.left.comp f.left
  right := g.right.comp f.right
  left_injective := g.left_injective.comp f.left_injective
  right_injective := g.right_injective.comp f.right_injective
  pairing_apply := by
    intro x y
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      g.pairing_apply, f.pairing_apply]

@[simp] theorem refl_left_apply (A : CoordinateBanana l r)
    (x : Fin l → F2) :
    (refl A).left x = x := rfl

@[simp] theorem refl_right_apply (A : CoordinateBanana l r)
    (y : Fin r → F2) :
    (refl A).right y = y := rfl

@[simp] theorem comp_left_apply
    (g : Embedding B C) (f : Embedding A B)
    (x : Fin l → F2) :
    (g.comp f).left x = g.left (f.left x) := rfl

@[simp] theorem comp_right_apply
    (g : Embedding B C) (f : Embedding A B)
    (y : Fin r → F2) :
    (g.comp f).right y = g.right (f.right y) := rfl

end Embedding

end CoordinateBanana

namespace PerfectCopyMatrices

variable {d n : ℕ} (E : PerfectCopyMatrices d n)

/-- A perfect-copy matrix pair is exactly a coordinate embedding
`B_d ↪ B_n` of the standard perfect BANANA structures. -/
def toBananaEmbedding :
    CoordinateBanana.Embedding
      (CoordinateBanana.perfect d)
      (CoordinateBanana.perfect n) where
  left := E.leftMap
  right := E.rightMap
  left_injective := E.leftMap_injective
  right_injective := E.rightMap_injective
  pairing_apply := by
    intro x y
    simpa using E.pairing_apply x y

@[simp] theorem toBananaEmbedding_left_apply (x : Fin d → F2) :
    E.toBananaEmbedding.left x = E.leftMap x := rfl

@[simp] theorem toBananaEmbedding_right_apply (y : Fin d → F2) :
    E.toBananaEmbedding.right y = E.rightMap y := rfl

end PerfectCopyMatrices

end SuccessorTree.NonPrecompact
