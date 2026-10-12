import SuccessorTree.V10.LevelRemovalType
import SuccessorTree.V10.ParameterLetterUniqueness
import Mathlib.Tactic

/-!
# Valid canonical last-ordinary E columns survive coordinate deletion

For a complete successor L+ record Q with old predecessor length ell+1,
remove an earlier ordinary coordinate m<ell+1. The old last ordinary
vertex is the new last ordinary vertex. If its original E free cut is f,
the shortened cut is exactly deleteAtCut m f.

We prove that the shortened complete L+ record still satisfies
ValidNewOrdinaryColumn at this transported cut: its E column is the
correct initial segment, every reverse E pair vanishes, and all
directed L pairs outside the free E socle are absent.

This is a finite record theorem. It does not assume or prove global
M2, a complete above-gap successor law, or the L-only age test.
-/

namespace SuccessorTree.V10

/-- A predecessor coordinate i in the shortened source level
corresponds to old coordinate deleteAt m i before the removed
ordinary vertex. -/
def deletedOldPredecessorIndex
    (ell m : Nat) (hm : m < ell + 1) (i : Fin ell) :
    Fin (ell + 1) :=
  ⟨deleteAt m i.val, by
    by_cases hi : i.val < m
    · rw [deleteAt_below m i.val hi]
      omega
    · rw [deleteAt_above m i.val (by omega)]
      omega⟩

/-- Last ordinary vertex renumbering across an earlier deletion. -/
theorem deleteTypeCoordinate_oldLast
    (ell m : Nat) (hm : m < ell + 1) :
    deleteTypeCoordinate m (ell + 2) (by omega)
        (some (Fin.last ell)) =
      some (Fin.last (ell + 1)) := by
  apply congrArg some
  apply Fin.ext
  change deleteAt m ell = ell + 1
  rw [deleteAt_above m ell (by omega)]

/-- Old predecessor coordinate corresponding to a new source
coordinate, including the full dependent Fin bounds. -/
theorem deleteTypeCoordinate_oldPredecessor
    (ell m : Nat) (hm : m < ell + 1) (i : Fin ell) :
    deleteTypeCoordinate m (ell + 2) (by omega)
        (some (i.castSucc : Fin (ell + 1))) =
      some ((deletedOldPredecessorIndex ell m hm i).castSucc) := by
  apply congrArg some
  apply Fin.ext
  rfl

/-- The shortened free E-socle lies within the shortened predecessor
ordinal. -/
theorem deleteAtCut_le_shorter
    (ell m f : Nat) (hm : m < ell + 1) (hf : f ≤ ell + 1) :
    deleteAtCut m f ≤ ell := by
  unfold deleteAtCut
  split_ifs <;> omega

/-- A valid canonical last ordinary column remains valid after
deleting an earlier ordinary coordinate, at the uniquely prescribed
transported free cut. No auxiliary age or successor hypothesis. -/
theorem validNewOrdinaryColumn_deleteOrdinary
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat) (hm : m < ell + 1)
    (hf : f ≤ ell + 1)
    (hValid : ValidNewOrdinaryColumn Q f) :
    ValidNewOrdinaryColumn (Q.deleteOrdinary m (by omega))
      (deleteAtCut m f) := by
  have hOldLast := deleteTypeCoordinate_oldLast ell m hm
  have hOldPre (i : Fin ell) :=
    deleteTypeCoordinate_oldPredecessor ell m hm i
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let j : Fin (ell + 1) := deletedOldPredecessorIndex ell m hm i
    have hRaw :
        Q.eRelation (some j.castSucc) (some (Fin.last (ell + 1))) =
          decide (i.val < deleteAtCut m f) := by
      calc
        Q.eRelation (some j.castSucc) (some (Fin.last (ell + 1))) =
            decide (j.val < f) := hValid.oldToNewE j
        _ = decide (i.val < deleteAtCut m f) := by
          by_cases hNew : i.val < deleteAtCut m f
          · have hOld : j.val < f :=
              (deleteAt_lt_iff_lt_deleteAtCut m f i.val).2 hNew
            simp [hOld, hNew]
          · have hOld : ¬ j.val < f := by
              intro hj
              exact hNew
                ((deleteAt_lt_iff_lt_deleteAtCut m f i.val).1 hj)
            simp [hOld, hNew]
    change Q.eRelation
      (deleteTypeCoordinate m (ell + 2) (by omega)
        (some (i.castSucc : Fin (ell + 1))))
      (deleteTypeCoordinate m (ell + 2) (by omega)
        (some (Fin.last ell))) =
      decide (i.val < deleteAtCut m f)
    rw [hOldPre i, hOldLast]
    exact hRaw
  · intro i
    let j : Fin (ell + 1) := deletedOldPredecessorIndex ell m hm i
    have hRaw :
        Q.eRelation (some (Fin.last (ell + 1))) (some j.castSucc) =
          false := hValid.newToOldE j
    change Q.eRelation
      (deleteTypeCoordinate m (ell + 2) (by omega)
        (some (Fin.last ell)))
      (deleteTypeCoordinate m (ell + 2) (by omega)
        (some (i.castSucc : Fin (ell + 1)))) = false
    rw [hOldLast, hOldPre i]
    exact hRaw
  · intro i hi r
    let j : Fin (ell + 1) := deletedOldPredecessorIndex ell m hm i
    have hOldLe : f ≤ j.val := by
      change f ≤ deleteAt m i.val
      by_contra h
      have hLt : deleteAt m i.val < f := by omega
      have hNewLt :=
        (deleteAt_lt_iff_lt_deleteAtCut m f i.val).mp hLt
      omega
    have hRaw := hValid.noNewBinaryBeyondCut j hOldLe r
    change Q.lReduct.binary
      (deleteTypeCoordinate m (ell + 2) (by omega)
        (some (i.castSucc : Fin (ell + 1))))
      (deleteTypeCoordinate m (ell + 2) (by omega)
        (some (Fin.last ell))) r = false ∧
      Q.lReduct.binary
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (some (Fin.last ell)))
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (some (i.castSucc : Fin (ell + 1)))) r = false
    rw [hOldPre i, hOldLast]
    exact hRaw

end SuccessorTree.V10
