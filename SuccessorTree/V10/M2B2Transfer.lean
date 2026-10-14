import SuccessorTree.V10.M2ShapeMapCompatReflection
import SuccessorTree.V10.M2TwoTypeImageCompatibility
import Mathlib.Tactic

/-!
# B2 transfer through the first intrinsic deletion factor

Every concrete Kpt shape map reflects ordinary L+ compatibility on
source types by complete retained-record recovery. The nonedge joint
source witness gives preservation of that compatibility under any
second map. Hence the ordinary compatibility of D(T),D(U) implies
compatibility of F(T),F(U) for ANY shape maps D and F. The special
intrinsic deletion D of M2 needs no additional compatibility axiom.
-/
namespace SuccessorTree.V10

theorem shapeMap_transfers_ordinary_compatibility
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F D : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (T U : PartialTypeWithE n db du dd)
    (hn : 0 < n)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hCompatibleAfterD :
      let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
      let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
      ∃ h : LevelTree.lev (D ti) = LevelTree.lev (D tj),
        SameOrdinaryAtCut (D ti).1.2
          (cast (congrArg (fun k => PartialTypeWithE k db du dd)
            h.symm) (D tj).1.2)) :
    let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
    let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
    ∃ h : LevelTree.lev (F ti) = LevelTree.lev (F tj),
      SameOrdinaryAtCut (F ti).1.2
        (cast (congrArg (fun k => PartialTypeWithE k db du dd)
          h.symm) (F tj).1.2) := by
  have hSource := shapeMap_reflects_source_compatibility
    family D T U hT hU hCompatibleAfterD
  exact shapeMap_preserves_source_compatibility
    family F T U hn hT hU hSource

end SuccessorTree.V10
