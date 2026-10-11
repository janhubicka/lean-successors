import SuccessorTree.V10.LevelRemovalIntrinsicAdmissible
import SuccessorTree.V10.LevelRemovalUniformImageGuard
import Mathlib.Tactic

/-!
# Intrinsic deleted Kpt values at the M2 boundary and above

A source-image gap supplies a genuine weak image successor with a
strictly low E cut. For a boundary source node a, one may choose
a genuine successor b and a finite witness of F(b), but the
DELETED VALUE must be defined from the fixed complete record of
F(a), not from the chosen b or its witness.

The upper-witness admissibility lemma provides exactly this:
a guarded witness of F(b) certifies the intrinsic deletion of
the lower prefix F(a). The same argument certifies the intrinsic
deletion of any upper image F(z) with b <= z.

This proves membership of these local candidate values only.
The all-level uniform map, its level function, weak successor
preservation, and M2 factorization remain separate obligations.
-/

namespace SuccessorTree.V10

/-- At the first source level after a genuine image gap, the raw
deleted complete record of F(a) is admissible. The chosen actual
successor serves only to prove the certificate; it is not used
to DEFINE the candidate output. -/
theorem boundary_deleted_image_type_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a : AdmissibleKptNode family)
    (hPrev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a)) :
    let m := LevelTree.lev (F a) - 1
    ∃ (hm : m < (F a).1.1),
      IsAdmissibleRawType family
        (⟨(F a).1.1 - 1,
          (F a).1.2.deleteOrdinary m hm⟩ :
            RawPartialTypeNode db du dd) := by
  let m := LevelTree.lev (F a) - 1
  have hm : m < (F a).1.1 := by
    dsimp [m]
    change LevelTree.lev (F a) - 1 < LevelTree.lev (F a)
    omega
  obtain ⟨b,p,c,A,v,hSucc,hv,hAvoid,hRep,hGuard⟩ :=
    boundary_gap_guarded_successor_witness_exists
      family F q a hPrev hGap
  have hCover : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hFaLtFb : LevelTree.lev (F a) < LevelTree.lev (F b) :=
    F.level_lt_of_level_lt (LevelTree.lt_level_lt hCover.lt)
  have hRepLevel : LevelTree.lev (F b) = A.freeLevel v := by
    have hh := congrArg Sigma.fst hRep
    change (F b).1.1 = A.freeLevel v at hh
    exact hh
  have hNext : m + 1 < A.size := by
    have hVFree := A.freeLevel_le v
    dsimp [m]
    omega
  have hGuardM : A.freeLevel (m + 1) < m := by
    have hEq : m + 1 = LevelTree.lev (F a) := by
      dsimp [m]
      omega
    rw [hEq]
    exact hGuard
  have hLower : F a ≤ F b := F.map_le_of_le hCover.le
  exact ⟨hm,
    admissible_deleted_lower_of_guarded_upper family
      (F a) (F b) hLower m hm A v hv hRep hAvoid hNext hGuardM⟩

/-- For ANY upper source z above the selected genuine source
successor b, the deletion of the fixed complete record F(z)
is admissible. The bound on the necessary E column holds in
every finite representative of F(z), so no preferred witness
enters the candidate value. -/
theorem upper_deleted_image_type_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q a b z : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hPrev : LevelTree.lev q + 1 = LevelTree.lev a)
    (hGap : LevelTree.lev (F q) + 1 < LevelTree.lev (F a))
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hbz : b ≤ z) :
    let m := LevelTree.lev (F a) - 1
    ∃ (hm : m < (F z).1.1),
      IsAdmissibleRawType family
        (⟨(F z).1.1 - 1,
          (F z).1.2.deleteOrdinary m hm⟩ :
            RawPartialTypeNode db du dd) := by
  let m := LevelTree.lev (F a) - 1
  obtain ⟨A,v,hv,hAvoid,hRep⟩ := (F z).2
  have hCover : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hFaLtFb : LevelTree.lev (F a) < LevelTree.lev (F b) :=
    F.level_lt_of_level_lt (LevelTree.lt_level_lt hCover.lt)
  have hFbLeFz : F b ≤ F z := F.map_le_of_le hbz
  have hFaLtFz : LevelTree.lev (F a) < LevelTree.lev (F z) :=
    lt_of_lt_of_le hFaLtFb (LevelTree.level_le_of_le hFbLeFz)
  have hm : m < (F z).1.1 := by
    dsimp [m]
    change LevelTree.lev (F a) - 1 < LevelTree.lev (F z)
    omega
  have hGuard :=
    gap_guard_in_every_upper_image_witness
      family F q a b z p c hPrev hGap hSucc hbz A v hv hRep
  have hRepLevel : LevelTree.lev (F z) = A.freeLevel v := by
    have hh := congrArg Sigma.fst hRep
    change (F z).1.1 = A.freeLevel v at hh
    exact hh
  have hNext : m + 1 < A.size := by
    have hVFree := A.freeLevel_le v
    dsimp [m]
    omega
  have hGuardM : A.freeLevel (m + 1) < m := by
    have hEq : m + 1 = LevelTree.lev (F a) := by
      dsimp [m]
      omega
    rw [hEq]
    exact hGuard
  exact ⟨hm,
    admissible_deleted_lower_of_guarded_upper family
      (F z) (F z) le_rfl m hm A v hv hRep hAvoid hNext hGuardM⟩

end SuccessorTree.V10
