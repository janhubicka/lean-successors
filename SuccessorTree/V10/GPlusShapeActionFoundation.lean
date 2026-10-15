import SuccessorTree.V10.GPlusOrderedEmbedding
import SuccessorTree.V10.M2CapRetainedAtoms
import SuccessorTree.V10.M2TwoTypeImageCompatibility
import SuccessorTree.V10.M2ShapeMapCompatReflection

/-!
# Observation 6.42 foundation: a genuine G+ vertex from a ShapeMap image cut

This file builds the actual finite G+ object needed for the manuscript's
induced action.  No representation interface is assumed.

For a valid finite G+ code A, choose one genuine finite partial-structure
witness only to construct the standard neutral cap.  Apply a genuine Kpt
ShapeMap F to that admissible cap, then cut the image at

  lambda(|A|-1)+1.

The cut is an admissible Kpt ancestor.  A generic admissible-node-to-G+
constructor then chooses a representing finite partial structure and takes
its genuine initial segment at the node level.  Hence the result is a real
forbidden-free G+ vertex.

The subsequent Observation 6.42 proof must show that this vertex is
independent of the chosen cap witness/representative pair, reflects equality,
and preserves all G+ atoms.  Those claims are deliberately NOT assumed here.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace AdmissibleKptNode

/-- One finite partial structure witnessing admissibility. -/
noncomputable def witnessStructure (N : AdmissibleKptNode family) :
    EnumeratedPartialStructure db du dd :=
  Classical.choose N.property

/-- The represented vertex in the chosen admissibility witness. -/
noncomputable def witnessVertex (N : AdmissibleKptNode family) : Nat :=
  Classical.choose (Classical.choose_spec N.property)

/-- Exact data supplied by admissibility of the chosen witness. -/
theorem witness_spec (N : AdmissibleKptNode family) :
    N.witnessVertex < N.witnessStructure.size ∧
    (∀ bad, bad ∈ family → bad.Avoids N.witnessStructure.L) ∧
    N.1 = N.witnessStructure.rawTypeAtFree N.witnessVertex :=
  Classical.choose_spec (Classical.choose_spec N.property)

/-- The node level lies inside every chosen finite witness. -/
theorem level_le_witness_size (N : AdmissibleKptNode family) :
    N.1.1 ≤ N.witnessStructure.size := by
  have hv := (N.witness_spec).1
  have hNode := (N.witness_spec).2.2
  have hLevel := congrArg
    (fun Q : RawPartialTypeNode db du dd => Q.1) hNode
  change N.1.1 = N.witnessStructure.freeLevel N.witnessVertex at hLevel
  have hFree := N.witnessStructure.freeLevel_le N.witnessVertex
  omega

/-- Every positive-level admissible Kpt node canonically yields the
G+ vertex given by its finite ordinary socle.  The implementation uses
a witness, but the returned code is the literal initial finite table. -/
noncomputable def toGPlus
    (N : AdmissibleKptNode family) (hPos : 0 < N.1.1) :
    FiniteGPlusVertex family := by
  let B := N.witnessStructure
  let hn : N.1.1 ≤ B.size := N.level_le_witness_size
  have hAvoid : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    (N.witness_spec).2.1
  let P := B.initialSegment N.1.1 hn
  exact finiteGPlusVertexOfEnumerated family P hPos
    (B.initialSegment_avoids family hAvoid N.1.1 hn)

/-- The resulting G+ code has exactly the Kpt node level as its size. -/
@[simp] theorem toGPlus_size
    (N : AdmissibleKptNode family) (hPos : 0 < N.1.1) :
    (N.toGPlus hPos).val.size = N.1.1 := by
  simp [toGPlus]

end AdmissibleKptNode

namespace FiniteGPlusVertex

/-- One genuine finite partial-structure witness for a valid G+ code. -/
noncomputable def chosenStructure (A : FiniteGPlusVertex family) :
    EnumeratedPartialStructure db du dd :=
  Classical.choose A.property

theorem chosenStructure_spec (A : FiniteGPlusVertex family) :
    A.val = FinitePartialCode.ofEnumerated A.chosenStructure ∧
    0 < A.chosenStructure.size ∧
    (∀ bad, bad ∈ family → bad.Avoids A.chosenStructure.L) :=
  Classical.choose_spec A.property

theorem chosenStructure_size (A : FiniteGPlusVertex family) :
    A.chosenStructure.size = A.val.size := by
  have h := congrArg FinitePartialCode.size (A.chosenStructure_spec).1
  exact h.symm

/-- The standard admissible neutral cap over the entire finite code. -/
noncomputable def canonicalCap (A : FiniteGPlusVertex family) :
    AdmissibleKptNode family :=
  NonedgePadding.socleCapNode family A.chosenStructure
    (A.chosenStructure_spec).2.2

@[simp] theorem canonicalCap_level (A : FiniteGPlusVertex family) :
    LevelTree.lev A.canonicalCap = A.val.size := by
  change A.chosenStructure.size = A.val.size
  exact A.chosenStructure_size

end FiniteGPlusVertex

/-- The manuscript cut immediately above the image of A's last coordinate. -/
noncomputable def gPlusShapeImageCut
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) : Nat :=
  kptShapeLevelMap family F (A.val.size - 1) + 1

theorem gPlusShapeImageCut_pos
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    0 < gPlusShapeImageCut F A := by
  unfold gPlusShapeImageCut
  omega

/-- The cut lies inside the image of the canonical cap. -/
theorem gPlusShapeImageCut_le_capImage
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    gPlusShapeImageCut F A ≤ LevelTree.lev (F A.canonicalCap) := by
  have hPos := finiteGPlusVertex_size_pos A
  have hLast : A.val.size - 1 < A.val.size := by omega
  have hStrict := kptShapeLevelMap_strictMono family F hLast
  have hCap := kptShapeLevelMap_eq family F A.canonicalCap
  rw [A.canonicalCap_level] at hCap
  unfold gPlusShapeImageCut
  omega

/-- The actual admissible image prefix corresponding to the manuscript
vertex v(F(S),F(T)).  This is still a Kpt node; the next definition turns
its ordinary socle into a genuine G+ vertex. -/
noncomputable def gPlusShapeImageNode
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) : AdmissibleKptNode family :=
  admissibleKptAncestor (F A.canonicalCap)
    (gPlusShapeImageCut F A) (gPlusShapeImageCut_le_capImage F A)

@[simp] theorem gPlusShapeImageNode_level
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    LevelTree.lev (gPlusShapeImageNode F A) = gPlusShapeImageCut F A := by
  exact LevelTree.level_ancestor _ _ _

/-- Candidate action of F on an actual G+ vertex, obtained from the
genuine finite ordinary socle of the image prefix. -/
noncomputable def gPlusShapeImage
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) : FiniteGPlusVertex family :=
  (gPlusShapeImageNode F A).toGPlus
    (by rw [gPlusShapeImageNode_level]; exact gPlusShapeImageCut_pos F A)

@[simp] theorem gPlusShapeImage_size
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : FiniteGPlusVertex family) :
    (gPlusShapeImage F A).val.size = gPlusShapeImageCut F A := by
  simp [gPlusShapeImage]

end SuccessorTree.V10
