import SuccessorTree.V10.GPlusOrdinaryCode
import Mathlib.Tactic

/-!
# Observation 6.42: equality of G+ codes is ordinary-type compatibility

The previous file proves the forward implication: equal complete ordinary
L+ records produce literally equal finite G+ codes.  Here we prove the
converse using the finite-table equivalence already constructed for the
exhaustive G+ enumeration.  Thus equality of finite codes is equivalent to
SameOrdinaryAtCut, not merely to the presence of positive edges.

In particular this is the exact source premise of the previously verified
shapeMap_preserves_source_compatibility.  Its reflected version uses
shapeMap_reflects_source_compatibility and full retained records.

This file does not assume the final G+ action or its functoriality.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Equality of the four finite atom tables forces equality of complete
ordinary socles, including both Boolean values and the auxiliary E table. -/
theorem sameOrdinary_of_ordinaryCode_eq
    {n : Nat} (T U : PartialTypeWithE n db du dd)
    (hCode :
      RawPartialTypeNode.ordinaryCode
        (⟨n,T⟩ : RawPartialTypeNode db du dd) =
      RawPartialTypeNode.ordinaryCode
        (⟨n,U⟩ : RawPartialTypeNode db du dd)) :
    SameOrdinaryAtCut T U := by
  let A : {C : FinitePartialCode db du dd // C.size = n} :=
    ⟨RawPartialTypeNode.ordinaryCode
      (⟨n,T⟩ : RawPartialTypeNode db du dd),rfl⟩
  let B : {C : FinitePartialCode db du dd // C.size = n} :=
    ⟨RawPartialTypeNode.ordinaryCode
      (⟨n,U⟩ : RawPartialTypeNode db du dd),rfl⟩
  have hAB : A = B := Subtype.ext hCode
  have hTables := congrArg
    (GPlusEnumeration.fixedSizeEquivTables (db:=db) (du:=du) (dd:=dd) n)
    hAB
  change
    ((fun i j t => T.lReduct.binary (some i) (some j) t),
      (fun i t => T.lReduct.unary (some i) t),
      (fun i t => T.lReduct.diagonal (some i) t),
      (fun i j => T.eRelation (some i) (some j))) =
    ((fun i j t => U.lReduct.binary (some i) (some j) t),
      (fun i t => U.lReduct.unary (some i) t),
      (fun i t => U.lReduct.diagonal (some i) t),
      (fun i j => U.eRelation (some i) (some j))) at hTables
  have hB := congrArg (fun p : FinitePartialTables db du dd n => p.1) hTables
  have hU := congrArg (fun p : FinitePartialTables db du dd n => p.2.1) hTables
  have hD := congrArg (fun p : FinitePartialTables db du dd n => p.2.2.1) hTables
  have hE := congrArg (fun p : FinitePartialTables db du dd n => p.2.2.2) hTables
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j t
    exact congrFun (congrFun (congrFun hB i) j) t
  · intro i t
    exact congrFun (congrFun hU i) t
  · intro i t
    exact congrFun (congrFun hD i) t
  · intro i j
    exact congrFun (congrFun hE i) j

/-- Complete ordinary compatibility is literally the equality of the
canonical finite tables. This is an induced, not merely positive, record. -/
theorem sameOrdinary_iff_ordinaryCode_eq
    {n : Nat} (T U : PartialTypeWithE n db du dd) :
    SameOrdinaryAtCut T U ↔
      RawPartialTypeNode.ordinaryCode
        (⟨n,T⟩ : RawPartialTypeNode db du dd) =
      RawPartialTypeNode.ordinaryCode
        (⟨n,U⟩ : RawPartialTypeNode db du dd) := by
  exact ⟨ordinaryCode_eq_of_sameOrdinary T U,
    sameOrdinary_of_ordinaryCode_eq T U⟩

/-- If genuine admissible Kpt nodes at one level represent the same
G+ vertex, then their entire ordinary L+ records agree. -/
theorem admissibleKpt_sameOrdinary_of_toGPlus_eq
    {n : Nat} (T U : PartialTypeWithE n db du dd)
    (hn : 0 < n)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hEqual :
      AdmissibleKptNode.toGPlus
        (⟨⟨n,T⟩,hT⟩ : AdmissibleKptNode family) hn =
      AdmissibleKptNode.toGPlus
        (⟨⟨n,U⟩,hU⟩ : AdmissibleKptNode family) hn) :
    SameOrdinaryAtCut T U := by
  have hCode := congrArg (fun A : FiniteGPlusVertex family => A.val) hEqual
  rw [AdmissibleKptNode.toGPlus_code,
      AdmissibleKptNode.toGPlus_code] at hCode
  exact sameOrdinary_of_ordinaryCode_eq T U hCode

/-- Applying a genuine shape map to two equal ordinary G+ source
codes preserves their full ordinary image compatibility.
This does not assume a G+ map: its conclusion concerns actual Kpt nodes. -/
theorem shapeMap_preserves_ordinaryCode_eq
    {n : Nat}
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (T U : PartialTypeWithE n db du dd)
    (hn : 0 < n)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hCode :
      RawPartialTypeNode.ordinaryCode
        (⟨n,T⟩ : RawPartialTypeNode db du dd) =
      RawPartialTypeNode.ordinaryCode
        (⟨n,U⟩ : RawPartialTypeNode db du dd)) :
    let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
    let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
    ∃ h : LevelTree.lev (F ti) = LevelTree.lev (F tj),
      SameOrdinaryAtCut (F ti).1.2
        (cast (congrArg (fun k => PartialTypeWithE k db du dd)
          h.symm) (F tj).1.2) := by
  exact shapeMap_preserves_source_compatibility
    family F T U hn hT hU (sameOrdinary_of_ordinaryCode_eq T U hCode)

end SuccessorTree.V10
