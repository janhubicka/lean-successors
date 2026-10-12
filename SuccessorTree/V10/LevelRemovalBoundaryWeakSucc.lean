import SuccessorTree.V10.LevelRemovalCrossGapPrefix
import SuccessorTree.V10.LevelRemovalGapColumn
import Mathlib.Tactic

/-!
# The weak image successor at the lower crossing survives level deletion

Suppose the source successor a -> b crosses into the first source
level n after an image gap, with b at level n and a at level n-1.
The original shape-preserving map F supplies a REAL weak successor
d of F(a), with d ≤ F(b). Its level is lev(F(a))+1, and the assumed
gap ensures that this is at most the deleted target coordinate
m = lev(F(b))-1.

The complete L+ prefix of F(b) represented by d is untouched by
deleting m. Hence d is below the raw coordinate-deleted image of b.
This is the exact low/crossing weak-successor witness needed for
the eventual M2 deletion ShapeMap; no unproved E-age condition or
global M2 map is used.
-/

namespace SuccessorTree.V10

/-- The weak image step at the source predecessor edge crossing into
the gap boundary remains below the COMPLETE raw deleted upper image.
The witness is the genuinely defined successor of F(a), not a
fabricated extension and not necessarily equal to F(b). -/
theorem weak_image_successor_below_deleted_boundary
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ a b : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hPrev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hGap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (hStep : (admissibleKptSTree family).succ a p c = some b)
    (hBAt : LevelTree.lev b = LevelTree.lev a₀) :
    let m := LevelTree.lev (F a₀) - 1
    ∃ (d : AdmissibleKptNode family),
      (admissibleKptSTree family).succ (F a) (p.map F) c = some d ∧
      ∃ hm : m < (F b).1.1,
        d.1 ≤ rawPartialTypeDeleteAt (F b).1 m hm := by
  let m := LevelTree.lev (F a₀) - 1
  have hCov : a ⋖ b := (admissibleKptSTree family).covBy_of_succ_eq_some hStep
  have hBL : LevelTree.lev b = LevelTree.lev a + 1 :=
    LevelTree.covBy_level_eq hCov
  have hAL : LevelTree.lev a = LevelTree.lev q₀ := by
    omega
  have hFAL : LevelTree.lev (F a) = LevelTree.lev (F q₀) :=
    F.level_eq_of_level_eq hAL
  have hFBL : LevelTree.lev (F b) = LevelTree.lev (F a₀) :=
    F.level_eq_of_level_eq hBAt
  obtain ⟨d,hMapped,hBelow⟩ := F.weak_succ' hStep
  have hMappedCov : F a ⋖ d :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hMapped
  have hDL : LevelTree.lev d = LevelTree.lev (F a) + 1 :=
    LevelTree.covBy_level_eq hMappedCov
  have hDLow : d.1.1 ≤ m := by
    change LevelTree.lev d ≤ m
    dsimp [m]
    omega
  have hm : m < (F b).1.1 := by
    change m < LevelTree.lev (F b)
    dsimp [m]
    omega
  have hRaw : d.1 ≤ rawPartialTypeDeleteAt (F b).1 m hm :=
    rawPartialTypePrefix_delete_above_cut
      (show d.1 ≤ (F b).1 from hBelow) m hDLow hm
  exact ⟨d,hMapped,hm,hRaw⟩

end SuccessorTree.V10
