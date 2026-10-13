import SuccessorTree.V10.ShapeMapAmbientOrdinaryTransport
import SuccessorTree.V10.NonedgePaddingCapTypes
import Mathlib.Tactic

/-!
# Compatibility of image socles from a single source witness

The M2 non-edge argument first realizes all compatible source types
as ordinary vertices in ONE admissible containing Kpt type. Once
that is done, the full parameter-prefix transport theorem identifies
their complete images with ordinary types of vertices inside ONE
image F(u). Thus their ordinary L+ socles agree automatically:
the common image socle does not depend on which distinguished
ordinary vertex was selected.

This theorem isolates this second half of the B2 argument. It
does not assume that arbitrary compatible source types already
possess a joint witness; the non-edge free-amalgamation construction
supplies that separate first half.
-/

namespace SuccessorTree.V10

/-- Equal image lengths can be transported at the level of the
numerical record indices before comparing their common ordinary socles.
Keeping the index variables explicit avoids dependent elimination on
the underlying subtype-valued image nodes. -/
theorem sameOrdinaryAtCut_of_jointOrdinaryTypes
    {ell db du dd : Nat}
    (Q : PartialTypeWithE ell db du dd)
    (i j : Nat) (hi : i < ell) (hj : j < ell)
    (n m : Nat) (hn : n ≤ ell) (hm : m ≤ ell)
    (R : PartialTypeWithE n db du dd)
    (S : PartialTypeWithE m db du dd)
    (h : n = m)
    (hR : Q.ordinaryType i hi n hn = R)
    (hS : Q.ordinaryType j hj m hm = S) :
    SameOrdinaryAtCut R
      (cast (congrArg (fun k => PartialTypeWithE k db du dd) h.symm) S) := by
  cases h
  change SameOrdinaryAtCut R S
  rw [← hR, ← hS]
  exact Q.ordinaryTypes_sameSocle i j hi hj hn

/-- After transporting two genuine source ordinary types into the
same F(u), their ordinary L+ records are identical. This is a
raw, representation-independent form using a common target level
and a cast for the dependent finite type. -/
theorem shapeMap_compatible_of_joint_ambient
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (A : EnumeratedPartialStructure db du dd)
    (v i j n : Nat)
    (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hiCut : i + 1 ≤ A.freeLevel v)
    (hjCut : j + 1 ≤ A.freeLevel v)
    (hiPos : 0 < A.freeLevel i)
    (hjPos : 0 < A.freeLevel j)
    (hiN : n ≤ A.freeLevel i)
    (hjN : n ≤ A.freeLevel j)
    (u ti tj : AdmissibleKptNode family)
    (hu : u.1 = A.rawTypeAtFree v)
    (hti : ti.1 =
      (⟨n,A.partialTypeAt n i⟩ : RawPartialTypeNode db du dd))
    (htj : tj.1 =
      (⟨n,A.partialTypeAt n j⟩ : RawPartialTypeNode db du dd)) :
    ∃ h : LevelTree.lev (F ti) = LevelTree.lev (F tj),
      SameOrdinaryAtCut (F ti).1.2
        (cast (congrArg
          (fun k => PartialTypeWithE k db du dd) h.symm)
          (F tj).1.2) := by
  obtain ⟨ai,hai,hfi,hli,hTypeI⟩ :=
    shapeMap_transports_ambient_ordinary_type family F A
      v i n hv hAvoid hiCut hiPos hiN u ti hu hti
  obtain ⟨aj,haj,hfj,hlj,hTypeJ⟩ :=
    shapeMap_transports_ambient_ordinary_type family F A
      v j n hv hAvoid hjCut hjPos hjN u tj hu htj
  have hLevelTI : LevelTree.lev ti = n := by
    have h := congrArg Sigma.fst hti
    exact h
  have hLevelTJ : LevelTree.lev tj = n := by
    have h := congrArg Sigma.fst htj
    exact h
  have hEq : LevelTree.lev (F ti) = LevelTree.lev (F tj) :=
    F.level_eq_of_level_eq (hLevelTI.trans hLevelTJ.symm)
  refine ⟨hEq, ?_⟩
  exact sameOrdinaryAtCut_of_jointOrdinaryTypes (F u).1.2
    (LevelTree.lev (F ai)) (LevelTree.lev (F aj)) hai haj
    (LevelTree.lev (F ti)) (LevelTree.lev (F tj)) hfi hfj
    (F ti).1.2 (F tj).1.2 hEq hTypeI hTypeJ

end SuccessorTree.V10
