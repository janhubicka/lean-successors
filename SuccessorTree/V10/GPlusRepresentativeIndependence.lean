import SuccessorTree.V10.GPlusImagePairRestriction
import Mathlib.Tactic

/-!
# Observation 6.42: independence of the representing pair

The manuscript assigns a G+ vertex to any strict admissible Kpt pair
P=(S,T) by v(P)=ordinaryCode(T restricted to level(S)+1).

For every genuine ShapeMap F, two possible constructions of its image
are now compared:
  1. take the image pair (F(S),F(T)) and form v(F(S),F(T));
  2. start from A=v(S,T), take its canonical neutral cap, apply F,
     and cut at lambda(|A|-1)+1.

The represented source prefix and its canonical cap have exactly the
same finite ordinary L+ code. Full image-code compatibility is
already a checked consequence of the genuine ShapeMap axioms;
the two actual image-pair restriction theorems then agree at the
common manuscript cut.

Consequently the candidate G+ image depends ONLY on the represented
G+ vertex, not on which admissible pair was used to represent it.
The reverse implication, all-atom induced G+ action and composition
are independent remaining steps, not assumptions of this module.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The two independently defined image cuts are the same natural
number, because v(S,T) has precisely level(S)+1 vertices. -/
theorem GPlusRepresentingPair.image_cut_eq_shapeImageCut
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).cut = gPlusShapeImageCut F P.vertex := by
  rw [P.image_cut F]
  unfold gPlusShapeImageCut
  rw [P.vertex_size]
  have hArg : LevelTree.lev P.lower = P.cut - 1 := by
    unfold GPlusRepresentingPair.cut
    omega
  rw [hArg]

/-- The original represented prefix and the canonical cap of its
finite G+ vertex have literally equal complete ordinary codes. -/
theorem GPlusRepresentingPair.representedNode_code_eq_cap
    (P : GPlusRepresentingPair family) :
    RawPartialTypeNode.ordinaryCode P.representedNode.1 =
      RawPartialTypeNode.ordinaryCode P.vertex.canonicalCap.1 := by
  calc
    RawPartialTypeNode.ordinaryCode P.representedNode.1 =
        P.vertex.val := (P.vertex_code).symm
    _ = RawPartialTypeNode.ordinaryCode P.vertex.canonicalCap.1 :=
        (FiniteGPlusVertex.canonicalCap_ordinaryCode P.vertex).symm

/-- The image vertex defined from ANY genuine representative pair
coincides with the canonical image of the represented G+ code.

This is the forward well-definedness content needed in Observation
6.42, for all finite ordinary L+ atoms (not just edges). -/
theorem GPlusRepresentingPair.image_vertex_eq_canonicalShapeImage
    (P : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (P.image F).vertex = gPlusShapeImage F P.vertex := by
  let d := (P.image F).cut
  have hPos : 0 < P.representedNode.1.1 := by
    change 0 < P.cut
    exact P.cut_pos
  have ha : d ≤ LevelTree.lev (F P.representedNode) :=
    LevelTree.level_le_of_le
      (P.image_representedNode_le_fullImage F)
  have hb : d ≤ LevelTree.lev (F P.vertex.canonicalCap) := by
    change (P.image F).cut ≤ LevelTree.lev (F P.vertex.canonicalCap)
    rw [P.image_cut_eq_shapeImageCut F]
    exact gPlusShapeImageCut_le_capImage F P.vertex
  have hRestricted :=
    shapeMap_preserves_equal_ordinaryCode_restrict
      F P.representedNode P.vertex.canonicalCap hPos
      P.representedNode_code_eq_cap d ha hb
  have hLeft :
      (P.image F).vertex.val =
        (RawPartialTypeNode.ordinaryCode
          (F P.representedNode).1).restrict d ha :=
    P.image_vertex_code_of_fullImage F
  have hRight :
      (gPlusShapeImage F P.vertex).val =
        (RawPartialTypeNode.ordinaryCode
          (F P.vertex.canonicalCap).1).restrict d hb := by
    simpa only [d, P.image_cut_eq_shapeImageCut F] using
      (gPlusShapeImage_code_of_fullCap F P.vertex)
  apply Subtype.ext
  exact hLeft.trans (hRestricted.trans hRight.symm)

/-- In particular, if two actual admissible representing pairs
define the same G+ vertex, they have the same image vertex under F.
No new assumption about how F acts on G+ is involved. -/
theorem GPlusRepresentingPair.image_vertex_eq_of_vertex_eq
    (P Q : GPlusRepresentingPair family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hPQ : P.vertex = Q.vertex) :
    (P.image F).vertex = (Q.image F).vertex := by
  calc
    (P.image F).vertex = gPlusShapeImage F P.vertex :=
      P.image_vertex_eq_canonicalShapeImage F
    _ = gPlusShapeImage F Q.vertex := by rw [hPQ]
    _ = (Q.image F).vertex :=
      (Q.image_vertex_eq_canonicalShapeImage F).symm

end SuccessorTree.V10
