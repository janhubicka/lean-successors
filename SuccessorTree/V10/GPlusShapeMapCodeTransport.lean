import SuccessorTree.V10.GPlusOrdinaryPrefix
import SuccessorTree.V10.M2TwoTypeImageCompatibility
import Mathlib.Tactic

/-!
# Observation 6.42: ShapeMaps transport equality of complete ordinary codes

The M2 verification already establishes that genuine ShapeMaps preserve
SameOrdinaryAtCut compatibility of admissible Kpt partial types.
The intrinsic-code theorem now identifies that compatibility with literal
equality of the corresponding finite ordinary L+ codes.

This module transports equality of finite ordinary source codes through
an arbitrary genuine Kpt ShapeMap, including the exact absence of both
directed binary atoms, unary/diagonal records and auxiliary E bits.

No abstract G+ representation or ShapeMap action on G+ is assumed.
The next bridge applies this to the actual image of representing pairs
and the shorter manuscript cut lambda(level(S))+1.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Equality of complete finite ordinary L+ codes is preserved by every
genuine admissible Kpt ShapeMap, at positive source levels. -/
theorem shapeMap_preserves_equal_ordinaryCode
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : AdmissibleKptNode family)
    (hPos : 0 < A.1.1)
    (hCode : RawPartialTypeNode.ordinaryCode A.1 =
      RawPartialTypeNode.ordinaryCode B.1) :
    RawPartialTypeNode.ordinaryCode (F A).1 =
      RawPartialTypeNode.ordinaryCode (F B).1 := by
  rcases A with ⟨⟨n,T⟩,hT⟩
  rcases B with ⟨⟨m,U⟩,hU⟩
  have hLevels : n = m := by
    have h := congrArg FinitePartialCode.size hCode
    exact h
  subst m
  have hOrd : SameOrdinaryAtCut T U :=
    sameOrdinary_of_ordinaryCode_eq T U hCode
  obtain ⟨hImageLev,hImageOrd⟩ :=
    shapeMap_preserves_source_compatibility family F T U hPos hT hU hOrd
  let a : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
  let b : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
  change (F a).1.1 = (F b).1.1 at hImageLev
  change RawPartialTypeNode.ordinaryCode (F a).1 =
    RawPartialTypeNode.ordinaryCode (F b).1
  cases hFA : (F a).1 with
  | mk na qa =>
    cases hFB : (F b).1 with
    | mk nb qb =>
      simp only [hFA, hFB] at hImageLev hImageOrd ⊢
      change na = nb at hImageLev
      subst nb
      have hOrdEq : SameOrdinaryAtCut qa qb := by
        simpa using hImageOrd
      exact ordinaryCode_eq_of_sameOrdinary qa qb hOrdEq

/-- Equality remains true after a shared smaller ordinary socle cut.
In particular it can be read at lambda(level(S))+1 rather than the
full image level lambda(level(S)+1). -/
theorem shapeMap_preserves_equal_ordinaryCode_restrict
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A B : AdmissibleKptNode family)
    (hPos : 0 < A.1.1)
    (hCode : RawPartialTypeNode.ordinaryCode A.1 =
      RawPartialTypeNode.ordinaryCode B.1)
    (d : Nat)
    (hdA : d ≤ (F A).1.1)
    (hdB : d ≤ (F B).1.1) :
    (RawPartialTypeNode.ordinaryCode (F A).1).restrict d hdA =
      (RawPartialTypeNode.ordinaryCode (F B).1).restrict d hdB := by
  have hImage := shapeMap_preserves_equal_ordinaryCode F A B hPos hCode
  have hCongr :
      ∀ (X Y : FinitePartialCode db du dd), X = Y →
        ∀ (hx : d ≤ X.size) (hy : d ≤ Y.size),
          X.restrict d hx = Y.restrict d hy := by
    intro X Y heq hx hy
    cases heq
    rfl
  exact hCongr _ _ hImage hdA hdB

end SuccessorTree.V10
