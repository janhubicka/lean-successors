import SuccessorTree.V10.GPlusShapeActionFoundation
import SuccessorTree.V10.PrescribedBoringData
import Mathlib.Tactic

/-!
# Canonical ordinary finite code of an admissible Kpt partial type

The representation of a finite G+ vertex by an admissible partial-type
node must not depend on the finite ambient witness selected by Classical.choose.
Its true code is the finite table of *ordinary* L+ atoms in the node record.

This file compares that intrinsic table with the previously constructed
G+ vertex obtained by taking a witnessed finite initial segment, and proves
that equal complete ordinary socles yield the same genuine G+ vertex.
This includes both directed orientations, false atoms, unary, diagonal and E.
No external age representation or abstract compatibility axioms are added.

The bridge to Observation 6.42 can now use the existing theorem
shapeMap_preserves_source_compatibility on actual Kpt nodes and transport
equal image ordinary records into equality of G+ vertices.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The intrinsic finite L+ table of the ordinary socle of a partial type.
All atoms are read at 'some i', never at the distinguished type vertex. -/
def RawPartialTypeNode.ordinaryCode
    (N : RawPartialTypeNode db du dd) : FinitePartialCode db du dd where
  size := N.1
  binary := fun i j t => N.2.lReduct.binary (some i) (some j) t
  unary := fun i t => N.2.lReduct.unary (some i) t
  diagonal := fun i t => N.2.lReduct.diagonal (some i) t
  eRelation := fun i j => N.2.eRelation (some i) (some j)

/-- The ordinary finite table of an actual initial partial type is
literally the canonical code of the matching genuine finite prefix. -/
theorem EnumeratedPartialStructure.initialSegment_code_eq_ordinaryCode
    (B : EnumeratedPartialStructure db du dd)
    (n v : Nat) (hn : n ≤ B.size) :
    FinitePartialCode.ofEnumerated (B.initialSegment n hn) =
      RawPartialTypeNode.ordinaryCode (⟨n,B.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
  calc
    FinitePartialCode.ofEnumerated (B.initialSegment n hn) =
        (FinitePartialCode.ofEnumerated B).restrict n hn :=
      (FinitePartialCode.ofEnumerated_initialSegment B n hn).symm
    _ = RawPartialTypeNode.ordinaryCode
          (⟨n,B.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := rfl

/-- The G+ vertex extracted from a genuine admissible partial type has
exactly its intrinsic ordinary table, not a witness-dependent code. -/
theorem AdmissibleKptNode.toGPlus_code
    (N : AdmissibleKptNode family) (hPos : 0 < N.1.1) :
    (N.toGPlus hPos).val = RawPartialTypeNode.ordinaryCode N.1 := by
  let B := N.witnessStructure
  let v := N.witnessVertex
  have hRaw : N.1 = B.rawTypeAtFree v := (N.witness_spec).2.2
  have hCut : N.1.1 = B.freeLevel v := congrArg Sigma.fst hRaw
  have hTyped : N.1 = (⟨N.1.1,B.partialTypeAt N.1.1 v⟩ :
      RawPartialTypeNode db du dd) := by
    calc
      N.1 = B.rawTypeAtFree v := hRaw
      _ = (⟨N.1.1,B.partialTypeAt N.1.1 v⟩ :
          RawPartialTypeNode db du dd) := by
        change (⟨B.freeLevel v,B.partialTypeAt (B.freeLevel v) v⟩ :
            RawPartialTypeNode db du dd) = _
        rw [←hCut]
  change FinitePartialCode.ofEnumerated
    (B.initialSegment N.1.1 N.level_le_witness_size) =
      RawPartialTypeNode.ordinaryCode N.1
  calc
    FinitePartialCode.ofEnumerated
        (B.initialSegment N.1.1 N.level_le_witness_size) =
      RawPartialTypeNode.ordinaryCode (⟨N.1.1,B.partialTypeAt N.1.1 v⟩ : RawPartialTypeNode db du dd) :=
          B.initialSegment_code_eq_ordinaryCode _ _ _
    _ = RawPartialTypeNode.ordinaryCode N.1 := by rw [hTyped]

/-- Equality of ordinary L+ socles, including all absent and E atoms,
is exactly strong enough to imply equality of their intrinsic codes. -/
theorem ordinaryCode_eq_of_sameOrdinary
    {n : Nat} (T U : PartialTypeWithE n db du dd)
    (h : SameOrdinaryAtCut T U) :
    RawPartialTypeNode.ordinaryCode (⟨n,T⟩ : RawPartialTypeNode db du dd) =
    RawPartialTypeNode.ordinaryCode (⟨n,U⟩ : RawPartialTypeNode db du dd) := by
  have hB : (fun i j t => T.lReduct.binary (some i) (some j) t) =
      (fun i j t => U.lReduct.binary (some i) (some j) t) := by
    funext i j t
    exact h.1 i j t
  have hU : (fun i t => T.lReduct.unary (some i) t) =
      (fun i t => U.lReduct.unary (some i) t) := by
    funext i t
    exact h.2.1 i t
  have hD : (fun i t => T.lReduct.diagonal (some i) t) =
      (fun i t => U.lReduct.diagonal (some i) t) := by
    funext i t
    exact h.2.2.1 i t
  have hE : (fun i j => T.eRelation (some i) (some j)) =
      (fun i j => U.eRelation (some i) (some j)) := by
    funext i j
    exact h.2.2.2 i j
  simp only [RawPartialTypeNode.ordinaryCode, hB, hU, hD, hE]

/-- Two genuine admissible nodes at the same positive level give
identical G+ vertices whenever their complete ordinary L+ data agree. -/
theorem admissibleKpt_toGPlus_eq_of_sameOrdinary
    {n : Nat} (T U : PartialTypeWithE n db du dd)
    (hn : 0 < n)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hComp : SameOrdinaryAtCut T U) :
    AdmissibleKptNode.toGPlus
      (⟨⟨n,T⟩,hT⟩ : AdmissibleKptNode family) hn =
    AdmissibleKptNode.toGPlus
      (⟨⟨n,U⟩,hU⟩ : AdmissibleKptNode family) hn := by
  apply Subtype.ext
  calc
    (AdmissibleKptNode.toGPlus (⟨⟨n,T⟩,hT⟩ : AdmissibleKptNode family) hn).val =
        RawPartialTypeNode.ordinaryCode (⟨n,T⟩ : RawPartialTypeNode db du dd) :=
      AdmissibleKptNode.toGPlus_code _ _
    _ = RawPartialTypeNode.ordinaryCode (⟨n,U⟩ : RawPartialTypeNode db du dd) :=
      ordinaryCode_eq_of_sameOrdinary T U hComp
    _ = (AdmissibleKptNode.toGPlus (⟨⟨n,U⟩,hU⟩ : AdmissibleKptNode family) hn).val :=
      (AdmissibleKptNode.toGPlus_code _ _).symm

end SuccessorTree.V10
