import SuccessorTree.V10.GPlusRepresentativeIndependence
import Mathlib.Tactic

/-!
# Observation 6.42: identity and composition of the induced G+ action

Every genuine finite G+ vertex has a canonical Kpt representing pair,
and the image of ANY representing pair agrees with the canonical
gPlusShapeImage construction.

Consequently the identity and composition laws follow from the
already verified ShapeMap.id and ShapeMap.comp operations applied
directly to representing pairs.  No additional local relation or
age assumption enters these laws.

The all-atom induced embedding and injectivity/reflection parts of
Observation 6.42 remain separate formalization obligations.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The canonical image construction agrees with the image of the
canonical representing pair of any genuine G+ vertex. -/
theorem gPlusShapeImage_eq_canonicalPairImage
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    gPlusShapeImage F A =
      ((GPlusRepresentingPair.canonical A).image F).vertex := by
  calc
    gPlusShapeImage F A =
        gPlusShapeImage F (GPlusRepresentingPair.canonical A).vertex := by
      rw [GPlusRepresentingPair.canonical_vertex A]
    _ = ((GPlusRepresentingPair.canonical A).image F).vertex :=
      (GPlusRepresentingPair.image_vertex_eq_canonicalShapeImage
        (GPlusRepresentingPair.canonical A) F).symm

/-- The genuine identity Kpt ShapeMap induces the identity G+ map. -/
theorem gPlusShapeImage_id
    (A : FiniteGPlusVertex family) :
    gPlusShapeImage
      (SuccessorTree.ShapeMap.id (admissibleKptSTree family)) A = A := by
  let P := GPlusRepresentingPair.canonical A
  have hRep : P.vertex = A := GPlusRepresentingPair.canonical_vertex A
  calc
    gPlusShapeImage
        (SuccessorTree.ShapeMap.id (admissibleKptSTree family)) A =
      gPlusShapeImage
        (SuccessorTree.ShapeMap.id (admissibleKptSTree family))
        P.vertex := by rw [hRep]
    _ = (P.image
        (SuccessorTree.ShapeMap.id (admissibleKptSTree family))).vertex :=
      (P.image_vertex_eq_canonicalShapeImage _).symm
    _ = P.vertex := rfl
    _ = A := hRep

/-- Applying G and then F to G+ agrees with the Kpt ShapeMap
composition F.comp G, without independently choosing source pairs. -/
theorem gPlusShapeImage_comp
    (F G : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    gPlusShapeImage (F.comp G) A =
      gPlusShapeImage F (gPlusShapeImage G A) := by
  let P := GPlusRepresentingPair.canonical A
  have hRep : P.vertex = A := GPlusRepresentingPair.canonical_vertex A
  calc
    gPlusShapeImage (F.comp G) A =
      gPlusShapeImage (F.comp G) P.vertex := by rw [hRep]
    _ = (P.image (F.comp G)).vertex :=
      (P.image_vertex_eq_canonicalShapeImage (F.comp G)).symm
    _ = ((P.image G).image F).vertex := rfl
    _ = gPlusShapeImage F (P.image G).vertex :=
      (P.image G).image_vertex_eq_canonicalShapeImage F
    _ = gPlusShapeImage F (gPlusShapeImage G P.vertex) := by
      rw [P.image_vertex_eq_canonicalShapeImage G]
    _ = gPlusShapeImage F (gPlusShapeImage G A) := by rw [hRep]

end SuccessorTree.V10
