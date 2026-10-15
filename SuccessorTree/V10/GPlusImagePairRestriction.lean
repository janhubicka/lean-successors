import SuccessorTree.V10.GPlusShapeMapCodeTransport
import Mathlib.Tactic

/-!
# Observation 6.42: image representing pairs are finite-code restrictions

The genuine image of a representing pair (S,T) is obtained from F(T)
at cut lambda(level(S))+1. To compare this with the canonical cap
representation, first use the actual Kpt prefix relation to show that
this image prefix already lies below F(T restricted to level(S)+1).
Its full induced G+ record is therefore the restriction of the
ordinary finite code of that image partial type.

The same restriction formula holds for the canonical image vertex
constructed from F(cap(A)). These are the two sides of the upcoming
representative-independence equality. No new age or G+ action interface
is postulated.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Kpt ancestry implies literal restriction of all four ordinary
finite atom tables. This is not merely preservation of positive atoms. -/
theorem admissibleKpt_ordinaryCode_of_le
    {A B : AdmissibleKptNode family} (hAB : A ≤ B) :
    RawPartialTypeNode.ordinaryCode A.1 =
      (RawPartialTypeNode.ordinaryCode B.1).restrict A.1.1
        (LevelTree.level_le_of_le hAB) := by
  exact (RawPartialTypeNode.ordinaryCode_isPrefix
    (show A.1 ≤ B.1 from hAB)).2

/-- In a genuine Kpt ShapeMap, the image of the manuscript's
represented prefix still contains the shorter image-pair cut.
Both prefixes lie below F(T), so uniqueness of ancestors forces
the image-pair representative below F(representedNode). -/
theorem GPlusRepresentingPair.image_representedNode_le_fullImage
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).representedNode ≤ F P.representedNode := by
  have hSource : P.representedNode ≤ P.upper :=
    admissibleKptAncestor_le P.upper P.cut P.cut_le_upper
  have hFull : F P.representedNode ≤ F P.upper :=
    F.map_le_of_le hSource
  have hSmall : (P.image F).representedNode ≤ F P.upper :=
    admissibleKptAncestor_le (F P.upper)
      (P.image F).cut (P.image F).cut_le_upper
  have hCut : LevelTree.lev ((P.image F).representedNode) =
      (P.image F).cut := rfl
  have hFullLevel : LevelTree.lev (F P.representedNode) =
      kptShapeLevelMap family F P.cut := by
    exact kptShapeLevelMap_eq family F P.representedNode
  have hPrev : LevelTree.lev P.lower < P.cut := by
    unfold GPlusRepresentingPair.cut
    omega
  have hStrict := kptShapeLevelMap_strictMono family F hPrev
  have hBound : LevelTree.lev ((P.image F).representedNode) ≤
      LevelTree.lev (F P.representedNode) := by
    rw [hCut, hFullLevel, P.image_cut F]
    omega
  rcases LevelTree.comparable_below hSmall hFull with h | h
  · exact h
  · have hLevels := LevelTree.level_le_of_le h
    have hEq : F P.representedNode = (P.image F).representedNode :=
      LevelTree.same_level_of_le h
        (Nat.le_antisymm hLevels hBound)
    exact le_of_eq hEq.symm

/-- The entire ordinary record of the actual image pair is the
restriction of F's image record of the represented source prefix. -/
theorem GPlusRepresentingPair.image_vertex_code_of_fullImage
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).vertex.val =
      (RawPartialTypeNode.ordinaryCode (F P.representedNode).1).restrict
        (P.image F).cut
        (LevelTree.level_le_of_le
          (P.image_representedNode_le_fullImage F)) := by
  calc
    (P.image F).vertex.val =
        RawPartialTypeNode.ordinaryCode (P.image F).representedNode.1 :=
      (P.image F).vertex_code
    _ = (RawPartialTypeNode.ordinaryCode
            (F P.representedNode).1).restrict
          (P.image F).cut
          (LevelTree.level_le_of_le
            (P.image_representedNode_le_fullImage F)) :=
      admissibleKpt_ordinaryCode_of_le
        (P.image_representedNode_le_fullImage F)

/-- The canonical image vertex of A is likewise precisely a finite-code
restriction of F's image of the actual canonical cap. -/
theorem gPlusShapeImage_code_of_fullCap
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    (gPlusShapeImage F A).val =
      (RawPartialTypeNode.ordinaryCode (F A.canonicalCap).1).restrict
        (gPlusShapeImageCut F A)
        (gPlusShapeImageCut_le_capImage F A) := by
  have hBelow :
      gPlusShapeImageNode F A ≤ F A.canonicalCap :=
    admissibleKptAncestor_le (F A.canonicalCap)
      (gPlusShapeImageCut F A)
      (gPlusShapeImageCut_le_capImage F A)
  calc
    (gPlusShapeImage F A).val =
        RawPartialTypeNode.ordinaryCode (gPlusShapeImageNode F A).1 := by
      exact AdmissibleKptNode.toGPlus_code _ _
    _ = (RawPartialTypeNode.ordinaryCode (F A.canonicalCap).1).restrict
          (gPlusShapeImageCut F A)
          (gPlusShapeImageCut_le_capImage F A) :=
      admissibleKpt_ordinaryCode_of_le hBelow

end SuccessorTree.V10
