import SuccessorTree.V10.GPlusCanonicalCapPrefix
import Mathlib.Tactic

/-!
# Observation 6.42: the genuine G+ image preserves and reflects prefix

Canonical neutral caps preserve the initial-segment order on finite G+
vertices. Genuine Kpt ShapeMaps preserve that order, and the short
image prefixes at the actual manuscript cuts retain it. Hence the
induced G+ image preserves the full finite-code prefix relation.

Conversely, if image(A) is a prefix of image(B), the strict global
level map forces size(A)<=size(B). Let C be the ACTUAL verified
positive-length prefix of B at size(A). Its image is another prefix
of image(B) of the same size as image(A); same-length prefix
uniqueness makes these images equal. The already proved injectivity
of the G+ image gives A=C, hence A is a prefix of B.

This particularly reflects incomparability, so the induced action
cannot create new binary or E relations between originally unrelated
branches. The explicit comparable-pair atom identities remain
the next separate verification step.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The image code size grows strictly with the original code size
because the Kpt global numerical level map is strictly increasing. -/
theorem gPlusShapeImage_size_lt_of_source_size_lt
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hSize : A.val.size < B.val.size) :
    (gPlusShapeImage F A).val.size <
      (gPlusShapeImage F B).val.size := by
  have hPosA := finiteGPlusVertex_size_pos A
  have hPosB := finiteGPlusVertex_size_pos B
  have hLast : A.val.size - 1 < B.val.size - 1 := by omega
  have hStrict := kptShapeLevelMap_strictMono family F hLast
  rw [gPlusShapeImage_size F A, gPlusShapeImage_size F B]
  change kptShapeLevelMap family F (A.val.size - 1) + 1 <
    kptShapeLevelMap family F (B.val.size - 1) + 1
  omega

/-- Smaller finite source sizes never yield larger G+ image sizes. -/
theorem gPlusShapeImage_size_le_of_source_size_le
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hSize : A.val.size ≤ B.val.size) :
    (gPlusShapeImage F A).val.size ≤
      (gPlusShapeImage F B).val.size := by
  rw [gPlusShapeImage_size F A, gPlusShapeImage_size F B]
  unfold gPlusShapeImageCut
  have hLast : A.val.size - 1 ≤ B.val.size - 1 := by omega
  exact Nat.add_le_add_right
    ((kptShapeLevelMap_strictMono family F).monotone hLast) 1

/-- Every genuine finite-code G+ prefix remains a finite-code prefix
under the image induced by ANY genuine Kpt ShapeMap. -/
theorem gPlusShapeImage_preserves_prefix
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hAB : A.val.IsPrefix B.val) :
    (gPlusShapeImage F A).val.IsPrefix
      (gPlusShapeImage F B).val := by
  have hCaps : A.canonicalCap ≤ B.canonicalCap :=
    A.canonicalCap_le_of_prefix B hAB
  have hImageCaps : F A.canonicalCap ≤ F B.canonicalCap :=
    F.map_le_of_le hCaps
  have hAUnder : gPlusShapeImageNode F A ≤ F A.canonicalCap :=
    admissibleKptAncestor_le (F A.canonicalCap) _
      (gPlusShapeImageCut_le_capImage F A)
  have hBUnder : gPlusShapeImageNode F B ≤ F B.canonicalCap :=
    admissibleKptAncestor_le (F B.canonicalCap) _
      (gPlusShapeImageCut_le_capImage F B)
  have hBelowTop : gPlusShapeImageNode F A ≤ F B.canonicalCap :=
    hAUnder.trans hImageCaps
  have hCutLe : gPlusShapeImageCut F A ≤ gPlusShapeImageCut F B := by
    have hSize := hAB.1
    have hSizeImage := gPlusShapeImage_size_le_of_source_size_le F A B hSize
    simpa only [gPlusShapeImage_size] using hSizeImage
  have hNodes : gPlusShapeImageNode F A ≤
      gPlusShapeImageNode F B := by
    rcases LevelTree.comparable_below hBelowTop hBUnder with h | h
    · exact h
    · have hLev := LevelTree.level_le_of_le h
      have hA : LevelTree.lev (gPlusShapeImageNode F A) =
          gPlusShapeImageCut F A := gPlusShapeImageNode_level F A
      have hB : LevelTree.lev (gPlusShapeImageNode F B) =
          gPlusShapeImageCut F B := gPlusShapeImageNode_level F B
      have hEqual : LevelTree.lev (gPlusShapeImageNode F B) =
          LevelTree.lev (gPlusShapeImageNode F A) := by omega
      have hEq := LevelTree.same_level_of_le h hEqual
      exact le_of_eq hEq.symm
  have hPosA : 0 < (gPlusShapeImageNode F A).1.1 := by
    change 0 < gPlusShapeImageCut F A
    exact gPlusShapeImageCut_pos F A
  have hPosB : 0 < (gPlusShapeImageNode F B).1.1 := by
    change 0 < gPlusShapeImageCut F B
    exact gPlusShapeImageCut_pos F B
  exact admissibleKpt_toGPlus_isPrefix hNodes hPosA hPosB

/-- Reflection needs NO inverse ShapeMap: the real positive G+ prefix
B|size(A) exists, and same-size prefixes of one tree node are unique.
Injectivity then recovers the source prefix relation. -/
theorem gPlusShapeImage_reflects_prefix
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hImage : (gPlusShapeImage F A).val.IsPrefix
      (gPlusShapeImage F B).val) :
    A.val.IsPrefix B.val := by
  have hSize : A.val.size ≤ B.val.size := by
    by_contra hNot
    have hBA : B.val.size < A.val.size := by omega
    have hImageBA :=
      gPlusShapeImage_size_lt_of_source_size_lt F B A hBA
    have hImageLe := hImage.1
    omega
  let C := B.restrict A.val.size (finiteGPlusVertex_size_pos A) hSize
  have hCSize : C.val.size = A.val.size := rfl
  have hCB : C.val.IsPrefix B.val := ⟨hSize,rfl⟩
  have hImageCB := gPlusShapeImage_preserves_prefix F C B hCB
  have hSameSize :
      (gPlusShapeImage F A).val.size =
        (gPlusShapeImage F C).val.size := by
    rw [gPlusShapeImage_size F A, gPlusShapeImage_size F C]
    unfold gPlusShapeImageCut
    rw [hCSize]
  have hCodes :=
    FinitePartialCode.prefix_unique_at_size hImage hImageCB hSameSize
  have hSameVertex : gPlusShapeImage F A = gPlusShapeImage F C :=
    Subtype.ext hCodes
  have hAC : A = C :=
    gPlusShapeImage_injective F hSameVertex
  refine ⟨hSize, ?_⟩
  calc
    A.val = C.val := congrArg Subtype.val hAC
    _ = B.val.restrict A.val.size hSize := rfl

/-- In particular the genuine induced image neither introduces nor
loses comparability: both proper-prefix orientations are reflected. -/
theorem gPlusShapeImage_properPrefix_iff
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family) :
    (gPlusShapeImage F A).IsProperPrefix (gPlusShapeImage F B) ↔
      A.IsProperPrefix B := by
  constructor
  · intro h
    have hPrefix := gPlusShapeImage_reflects_prefix F A B h.1
    have hSize : A.val.size < B.val.size := by
      have hLe := hPrefix.1
      by_contra hNot
      have hSame : A.val.size = B.val.size := by omega
      have hImgSize : (gPlusShapeImage F A).val.size =
          (gPlusShapeImage F B).val.size := by
        rw [gPlusShapeImage_size F A, gPlusShapeImage_size F B]
        unfold gPlusShapeImageCut
        rw [hSame]
      omega
    exact ⟨hPrefix,hSize⟩
  · intro h
    exact ⟨gPlusShapeImage_preserves_prefix F A B h.1,
      gPlusShapeImage_size_lt_of_source_size_lt F A B h.2⟩

end SuccessorTree.V10
