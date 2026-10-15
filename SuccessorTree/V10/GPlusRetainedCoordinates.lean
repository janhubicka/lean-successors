import SuccessorTree.V10.GPlusShapeActionLaws
import Mathlib.Tactic

/-!
# Observation 6.42: retained coordinates in the finite G+ image code

For a valid G+ code A of positive size n, the genuine ShapeMap F has
one strictly increasing numerical level map lambda. Its canonical
image vertex has size lambda(n-1)+1. Every retained original index
i<n therefore maps to lambda(i) within this image code, including the
last old coordinate and all earlier coordinates.

This module constructs the exact finite coordinate inclusion and
the associated complete four-table pullback (directed binary, unary,
diagonal and E). The next lemma must use
shapeMap_recovers_complete_record to prove that this pulled-back
image code is literally A; the equality is not assumed here.

No new type-level representation, E on an L-only witness, or
relaxation of the v10 axioms is introduced.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FinitePartialCode

/-- Pull the entire finite atomic table back along an arbitrary
finite coordinate function, with no positivity-only weakening. -/
def reindex (C : FinitePartialCode db du dd)
    (n : Nat) (rho : Fin n → Fin C.size) :
    FinitePartialCode db du dd where
  size := n
  binary := fun i j t => C.binary (rho i) (rho j) t
  unary := fun i t => C.unary (rho i) t
  diagonal := fun i t => C.diagonal (rho i) t
  eRelation := fun i j => C.eRelation (rho i) (rho j)

@[simp] theorem reindex_size (C : FinitePartialCode db du dd)
    (n : Nat) (rho : Fin n → Fin C.size) :
    (C.reindex n rho).size = n := rfl

/-- Reindexing by the identity changes no finite L+ atomic data. -/
theorem reindex_self (C : FinitePartialCode db du dd) :
    C.reindex C.size (fun i => i) = C := by
  cases C
  rfl

end FinitePartialCode

/-- Retained original coordinate i has image address lambda(i),
which is strictly below the manuscript cut lambda(n-1)+1. -/
noncomputable def shapeImageRetainedIndex
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family)
    (i : Fin A.val.size) : Fin (gPlusShapeImageCut F A) := by
  let lambda := kptShapeLevelMap family F
  have hPos := finiteGPlusVertex_size_pos A
  have hLast : i.val ≤ A.val.size - 1 := by omega
  have hBound : lambda i.val < lambda (A.val.size - 1) + 1 := by
    rcases lt_or_eq_of_le hLast with hlt | heq
    · have h := kptShapeLevelMap_strictMono family F hlt
      change lambda i.val < lambda (A.val.size - 1) at h
      omega
    · rw [heq]
      omega
  exact ⟨lambda i.val, hBound⟩

@[simp] theorem shapeImageRetainedIndex_val
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) (i : Fin A.val.size) :
    (shapeImageRetainedIndex F A i).val =
      kptShapeLevelMap family F i.val := rfl

/-- Retained image coordinates are injective by strictness of lambda. -/
theorem shapeImageRetainedIndex_injective
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    Function.Injective (shapeImageRetainedIndex F A) := by
  intro i j hEq
  apply Fin.ext
  have hValues := congrArg Fin.val hEq
  change kptShapeLevelMap family F i.val =
    kptShapeLevelMap family F j.val at hValues
  exact (kptShapeLevelMap_strictMono family F).injective hValues

/-- The retained numerical inclusion preserves the original order. -/
theorem shapeImageRetainedIndex_strictMono
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    StrictMono (shapeImageRetainedIndex F A) := by
  intro i j hij
  change kptShapeLevelMap family F i.val <
    kptShapeLevelMap family F j.val
  exact kptShapeLevelMap_strictMono family F hij

/-- Reindex the actual output G+ code along the old retained
coordinates. Its size is the old code size; the next proof identifies
every one of its four finite atomic tables with the original code. -/
noncomputable def shapeImageRetainedCode
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) : FinitePartialCode db du dd :=
  (gPlusShapeImage F A).val.reindex A.val.size
    (fun i => Fin.cast (gPlusShapeImage_size F A).symm
      (shapeImageRetainedIndex F A i))

@[simp] theorem shapeImageRetainedCode_size
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    (shapeImageRetainedCode F A).size = A.val.size := rfl

end SuccessorTree.V10
