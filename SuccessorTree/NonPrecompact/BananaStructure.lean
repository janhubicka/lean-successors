import SuccessorTree.NonPrecompact.PairingCopies

/-!
# Standard-coordinate finite BANANA structures

This file mirrors the finite structure/embedding definition from the BANANA
manuscript in standard coordinates.  A structure has two finite-dimensional
F₂-vector-space sorts and an arbitrary bilinear pairing, represented by a
matrix.  An embedding is a pair of injective linear maps preserving the
pairing; consequently it preserves and reflects the binary relation
`E(x,y) ↔ β(x,y)=1` and preserves the two additions and zero constants.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- A finite BANANA structure in chosen bases. -/
structure BananaMatrixStructure (l r : ℕ) where
  pairing : Matrix (Fin l) (Fin r) F2

namespace BananaMatrixStructure

variable {l r : ℕ} (A : BananaMatrixStructure l r)

/-- Evaluation of the bilinear pairing. -/
def eval (x : Fin l → F2) (y : Fin r → F2) : F2 :=
  x ⬝ᵥ (A.pairing *ᵥ y)

/-- The binary relation in the BANANA language. -/
def edge (x : Fin l → F2) (y : Fin r → F2) : Prop :=
  A.eval x y = 1

end BananaMatrixStructure

/-- An embedding between finite BANANA structures in chosen bases. -/
structure BananaMatrixEmbedding
    {l r l' r' : ℕ}
    (A : BananaMatrixStructure l r)
    (B : BananaMatrixStructure l' r') where
  left : (Fin l → F2) →ₗ[F2] (Fin l' → F2)
  right : (Fin r → F2) →ₗ[F2] (Fin r' → F2)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  pairing_apply :
    ∀ x y, B.eval (left x) (right y) = A.eval x y

namespace BananaMatrixEmbedding

variable {l r l' r' : ℕ}
variable {A : BananaMatrixStructure l r}
variable {B : BananaMatrixStructure l' r'}
variable (f : BananaMatrixEmbedding A B)

@[simp] theorem left_zero : f.left 0 = 0 :=
  f.left.map_zero

@[simp] theorem right_zero : f.right 0 = 0 :=
  f.right.map_zero

@[simp] theorem left_add (x y : Fin l → F2) :
    f.left (x + y) = f.left x + f.left y :=
  f.left.map_add x y

@[simp] theorem right_add (x y : Fin r → F2) :
    f.right (x + y) = f.right x + f.right y :=
  f.right.map_add x y

/-- Pairing preservation is equivalent to preservation and reflection of
the manuscript's relation `E`. -/
theorem edge_iff (x : Fin l → F2) (y : Fin r → F2) :
    B.edge (f.left x) (f.right y) ↔ A.edge x y := by
  unfold BananaMatrixStructure.edge
  rw [f.pairing_apply x y]

/-- Composition of BANANA embeddings. -/
def comp
    {l'' r'' : ℕ}
    {C : BananaMatrixStructure l'' r''}
    (g : BananaMatrixEmbedding B C)
    (f : BananaMatrixEmbedding A B) :
    BananaMatrixEmbedding A C where
  left := g.left.comp f.left
  right := g.right.comp f.right
  left_injective := g.left_injective.comp f.left_injective
  right_injective := g.right_injective.comp f.right_injective
  pairing_apply := by
    intro x y
    exact (g.pairing_apply (f.left x) (f.right y)).trans
      (f.pairing_apply x y)

end BananaMatrixEmbedding

/-- The standard perfect pairing `B_d`. -/
def perfectBanana (d : ℕ) : BananaMatrixStructure d d where
  pairing := 1

@[simp] theorem perfectBanana_eval
    {d : ℕ} (x y : Fin d → F2) :
    (perfectBanana d).eval x y = x ⬝ᵥ y := by
  simp [BananaMatrixStructure.eval, perfectBanana]

namespace BananaMatrixEmbedding

/-- A BANANA embedding between standard perfect pairings is exactly a
`PerfectPairEmbedding`. -/
def toPerfectPairEmbedding
    {d n : ℕ}
    (f :
      BananaMatrixEmbedding (perfectBanana d) (perfectBanana n)) :
    PerfectPairEmbedding d n where
  left := f.left
  right := f.right
  left_injective := f.left_injective
  right_injective := f.right_injective
  pairing_apply := by
    intro x y
    simpa only [perfectBanana_eval] using f.pairing_apply x y

end BananaMatrixEmbedding

namespace PerfectPairEmbedding

variable {d n : ℕ} (E : PerfectPairEmbedding d n)

/-- A perfect-pair embedding is exactly a BANANA embedding between the
standard perfect structures. -/
def toBananaMatrixEmbedding :
    BananaMatrixEmbedding (perfectBanana d) (perfectBanana n) where
  left := E.left
  right := E.right
  left_injective := E.left_injective
  right_injective := E.right_injective
  pairing_apply := by
    intro x y
    simpa only [perfectBanana_eval] using E.pairing_apply x y

end PerfectPairEmbedding

namespace PerfectCopyMatrices

variable {d n : ℕ} (E : PerfectCopyMatrices d n)

/-- Coordinate matrix copies therefore induce embeddings in the finite
BANANA class itself. -/
def toBananaMatrixEmbedding :
    BananaMatrixEmbedding (perfectBanana d) (perfectBanana n) :=
  E.toPerfectPairEmbedding.toBananaMatrixEmbedding

end PerfectCopyMatrices

end SuccessorTree.NonPrecompact
