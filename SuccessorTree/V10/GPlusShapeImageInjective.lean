import SuccessorTree.V10.GPlusCanonicalCodeReconstruction
import Mathlib.Tactic

/-!
# Observation 6.42: equality reflection and injectivity on G+

The genuine shape image of a finite G+ vertex A has size
lambda(|A|-1)+1. Strict increase of lambda therefore ensures
that two equal image vertices have equally sized source vertices.

The checked retained-code reconstruction gives back every source
atom by applying the SAME numerical index map lambda(i) to the
finite image tables. Equality of image codes plus equality of source
sizes thus forces equality of all four source tables.

This proves injectivity of the actual G+ image construction, and
hence the reverse implication in the manuscript's Observation 6.42
once combined with genuine representative-pair independence. The
full induced relation identities and final Ramsey transfer are
distinct subsequent targets.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FinitePartialCode

/-- Equality of image finite codes and source lengths gives equal
pullbacks when the numerical reindexing coordinates agree. -/
theorem reindex_congr
    {C D : FinitePartialCode db du dd}
    (hCD : C = D)
    {n m : Nat} (hNM : n = m)
    (rhoC : Fin n → Fin C.size)
    (rhoD : Fin m → Fin D.size)
    (hRho : ∀ i : Fin n,
      (rhoC i).val = (rhoD (Fin.cast hNM i)).val) :
    C.reindex n rhoC = D.reindex m rhoD := by
  cases hCD
  cases hNM
  have hRhoEq : rhoC = rhoD := by
    funext i
    exact Fin.ext (hRho i)
  subst rhoD
  rfl

end FinitePartialCode

/-- Equality of two G+ image vertices forces equality of original
code lengths because the genuine Kpt ShapeMap has strictly increasing
global level map lambda. -/
theorem gPlusShapeImage_eq_source_sizes
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hImage : gPlusShapeImage F A = gPlusShapeImage F B) :
    A.val.size = B.val.size := by
  have hSize := congrArg
    (fun V : FiniteGPlusVertex family => V.val.size) hImage
  rw [gPlusShapeImage_size F A, gPlusShapeImage_size F B] at hSize
  have hLast :
      A.val.size - 1 = B.val.size - 1 := by
    unfold gPlusShapeImageCut at hSize
    have hLambda :
        kptShapeLevelMap family F (A.val.size - 1) =
        kptShapeLevelMap family F (B.val.size - 1) := by omega
    exact (kptShapeLevelMap_strictMono family F).injective hLambda
  have hPosA := finiteGPlusVertex_size_pos A
  have hPosB := finiteGPlusVertex_size_pos B
  omega

/-- Equal source sizes ensure that the actual retained-coordinate
pullback maps agree numerically. The finite code equality itself is
handled by FinitePartialCode.reindex_congr. -/
theorem shapeImageRetainedCode_eq_of_image_eq
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : FiniteGPlusVertex family)
    (hImage : gPlusShapeImage F A = gPlusShapeImage F B) :
    shapeImageRetainedCode F A = shapeImageRetainedCode F B := by
  have hSize : A.val.size = B.val.size :=
    gPlusShapeImage_eq_source_sizes F A B hImage
  have hCode := congrArg
    (fun V : FiniteGPlusVertex family => V.val) hImage
  have hValues (i : Fin A.val.size) :
      (Fin.cast (gPlusShapeImage_size F A).symm
          (shapeImageRetainedIndex F A i)).val =
      (Fin.cast (gPlusShapeImage_size F B).symm
          (shapeImageRetainedIndex F B (Fin.cast hSize i))).val := by
    change kptShapeLevelMap family F i.val =
      kptShapeLevelMap family F (Fin.cast hSize i).val
    rfl
  exact FinitePartialCode.reindex_congr hCode hSize
    (fun i => Fin.cast (gPlusShapeImage_size F A).symm
      (shapeImageRetainedIndex F A i))
    (fun i => Fin.cast (gPlusShapeImage_size F B).symm
      (shapeImageRetainedIndex F B i))
    hValues

/-- Every genuine Kpt ShapeMap induces an INJECTIVE map on the true
finite G+ vertices. The proof recovers the original four Boolean
tables from the equal image codes, rather than merely preserving
positive relations. -/
theorem gPlusShapeImage_injective
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    Function.Injective (gPlusShapeImage F) := by
  intro A B hImage
  have hPulled := shapeImageRetainedCode_eq_of_image_eq F A B hImage
  rw [shapeImageRetainedCode_eq F A,
      shapeImageRetainedCode_eq F B] at hPulled
  exact Subtype.ext hPulled

/-- The full iff of equality in Observation 6.42, for ANY two
genuine Kpt representing pairs and ANY genuine Kpt ShapeMap.
The forward half is representative independence; the reverse
half is finite-code recovery and injectivity of gPlusShapeImage. -/
theorem GPlusRepresentingPair.image_vertex_eq_iff_vertex_eq
    (P Q : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).vertex = (Q.image F).vertex ↔ P.vertex = Q.vertex := by
  constructor
  · intro hImages
    have hP := P.image_vertex_eq_canonicalShapeImage F
    have hQ := Q.image_vertex_eq_canonicalShapeImage F
    have h : gPlusShapeImage F P.vertex =
        gPlusShapeImage F Q.vertex := hP.symm.trans (hImages.trans hQ)
    exact gPlusShapeImage_injective F h
  · exact P.image_vertex_eq_of_vertex_eq Q F

end SuccessorTree.V10
