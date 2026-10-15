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

/-- Dependent image lengths are aligned once, before projecting the
full same-ordinary record to the on-carrier finite code. -/
private theorem ordinaryCode_eq_of_compatible_levels
    (A B : RawPartialTypeNode db du dd)
    (hLev : A.1 = B.1)
    (hComp : SameOrdinaryAtCut A.2
      (cast (congrArg (fun k => PartialTypeWithE k db du dd)
        hLev.symm) B.2)) :
    RawPartialTypeNode.ordinaryCode A =
      RawPartialTypeNode.ordinaryCode B := by
  rcases A with ⟨n,T⟩
  rcases B with ⟨m,U⟩
  change n = m at hLev
  subst m
  have hOrd : SameOrdinaryAtCut T U := by
    simpa using hComp
  exact ordinaryCode_eq_of_sameOrdinary T U hOrd

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
    exact congrArg FinitePartialCode.size hCode
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
  exact ordinaryCode_eq_of_compatible_levels
    (F a).1 (F b).1 hImageLev hImageOrd

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
