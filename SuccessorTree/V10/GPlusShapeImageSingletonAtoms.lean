import SuccessorTree.V10.GPlusShapeImageInjective
import Mathlib.Tactic

/-!
# Observation 6.42: exact unary and diagonal atoms of the G+ action

The original G+ vertex A is recovered from the actual image finite
code by reindexing along the genuine Kpt level map lambda. The last
original coordinate |A|-1 maps to lambda(|A|-1), which is precisely
the last coordinate of the image code, since the manuscript image
cut is lambda(|A|-1)+1.

This file extracts the resulting equalities for every unary predicate
and every diagonal binary atom, retaining both true and false values.
It does not assume G+ prefix comparability or invent a relational
action interface. Off-diagonal directed binary and E atoms require a
common larger cap and are treated separately.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FinitePartialCode

/-- Literal equality of complete finite tables also identifies unary
data at a corresponding coordinate. The Fin cast only transfers the
size equality already implied by code equality. -/
theorem unary_eq_of_eq
    {C D : FinitePartialCode db du dd}
    (h : C = D) (i : Fin D.size) (t : Fin du) :
    C.unary
      (Fin.cast (congrArg FinitePartialCode.size h).symm i) t =
    D.unary i t := by
  cases h
  rfl

theorem diagonal_eq_of_eq
    {C D : FinitePartialCode db du dd}
    (h : C = D) (i : Fin D.size) (t : Fin dd) :
    C.diagonal
      (Fin.cast (congrArg FinitePartialCode.size h).symm i) t =
    D.diagonal i t := by
  cases h
  rfl

end FinitePartialCode

/-- The image address of the old last coordinate is the actual last
coordinate of its shorter G+ image vertex. -/
theorem shapeImageRetainedLast_eq_last
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    Fin.cast (gPlusShapeImage_size F A).symm
      (shapeImageRetainedIndex F A A.last) =
    (gPlusShapeImage F A).last := by
  apply Fin.ext
  change kptShapeLevelMap family F (A.val.size - 1) =
    (gPlusShapeImage F A).val.size - 1
  rw [gPlusShapeImage_size F A]
  unfold gPlusShapeImageCut
  omega

/-- All actual unary G+ atoms are preserved exactly by the
induced image of a genuine Kpt ShapeMap, including their absence. -/
theorem gPlusShapeImage_preserves_unary
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) (t : Fin du) :
    finiteGPlusUnary (gPlusShapeImage F A) t =
      finiteGPlusUnary A t := by
  have hRec := shapeImageRetainedCode_eq F A
  have hAtom :=
    FinitePartialCode.unary_eq_of_eq hRec A.last t
  change (gPlusShapeImage F A).val.unary
    (Fin.cast (gPlusShapeImage_size F A).symm
      (shapeImageRetainedIndex F A A.last)) t =
    A.val.unary A.last t at hAtom
  rw [shapeImageRetainedLast_eq_last F A] at hAtom
  exact hAtom

/-- All actual diagonal binary G+ atoms are also preserved, with
no identification of loops and off-diagonal directed atoms. -/
theorem gPlusShapeImage_preserves_diagonal
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) (t : Fin dd) :
    finiteGPlusDiagonal (gPlusShapeImage F A) t =
      finiteGPlusDiagonal A t := by
  have hRec := shapeImageRetainedCode_eq F A
  have hAtom :=
    FinitePartialCode.diagonal_eq_of_eq hRec A.last t
  change (gPlusShapeImage F A).val.diagonal
    (Fin.cast (gPlusShapeImage_size F A).symm
      (shapeImageRetainedIndex F A A.last)) t =
    A.val.diagonal A.last t at hAtom
  rw [shapeImageRetainedLast_eq_last F A] at hAtom
  exact hAtom

end SuccessorTree.V10
