import SuccessorTree.V10.LevelRemovalTerminalLetter
import SuccessorTree.V10.LevelRemovalFreeCut
import SuccessorTree.V10.ParameterLetterUniqueness
import Mathlib.Tactic

/-!
# A valid ordinary E/successor column survives deletion below its last vertex

Let Q be a complete type on ell+2 ordinary coordinates and let its last
ordinary vertex ell+1 have a certified canonical free E cut f. Remove an
earlier ordinary coordinate m<ell+1. The last vertex is retained and its
new canonical cut is deleteAtCut m f. Every old E-column bit, reverse E-bit
and both directed binary no-new-tuples conditions are checked literally.

This is the other finite ingredient, beside unchanged terminal letters,
for the ABOVE-GAP weak successor case in M2. It does NOT postulate a new
successor axiom or establish parameter transport, a ShapeMap, or M2.
-/

namespace SuccessorTree.V10

/-- Address in the old socle of a retained ordinary coordinate below
the old LAST ordinary vertex. -/
def deleteBelowLastIndex (ell m : Nat) (hm : m < ell + 1)
    (i : Fin ell) : Fin (ell + 1) :=
  ⟨deleteAt m i.val, by
    by_cases h : i.val < m
    · rw [deleteAt_below m i.val h]
      omega
    · rw [deleteAt_above m i.val (by omega)]
      omega⟩

/-- Inserting the old address of a shortened ordinary coordinate
commutes with casting it into the complete old successor socle. -/
theorem deleteTypeCoordinate_before_last
    (ell m : Nat) (hm : m < ell + 1)
    (i : Fin ell) :
    deleteTypeCoordinate m (ell + 2) (by omega)
      (some (i.castSucc)) =
      some ((deleteBelowLastIndex ell m hm i).castSucc) := by
  apply congrArg some
  apply Fin.ext
  rfl

/-- The new free E cut after deleting coordinate m is bounded by
the shortened predecessor level ell, even when f was maximal. -/
theorem deleteAtCut_le_new_predecessor
    (ell m f : Nat)
    (hm : m < ell + 1)
    (hf : f ≤ ell + 1) :
    deleteAtCut m f ≤ ell := by
  unfold deleteAtCut
  by_cases h : m < f
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

/-- All three fields of the genuine ValidNewOrdinaryColumn record
are transported by actual coordinate deletion. The new last ordinary
vertex corresponds to the old last ordinary vertex; for each retained
old coordinate i its address is deleteAt m i. -/
theorem validNewColumn_deleteOrdinary
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m f : Nat)
    (hm : m < ell + 1)
    (hf : f ≤ ell + 1)
    (hValid : ValidNewOrdinaryColumn Q f) :
    ValidNewOrdinaryColumn
      (Q.deleteOrdinary m (by omega))
      (deleteAtCut m f) := by
  have hLast :
      deleteTypeCoordinate m (ell + 2) (by omega)
        (some (Fin.last ell)) =
        some (Fin.last (ell + 1)) := by
    simpa [terminalCoordinate] using
      (deleteTypeCoordinate_terminal ell m hm
        (some (0 : Fin 1)))
  refine { oldToNewE := ?_, newToOldE := ?_,
    noNewBinaryBeyondCut := ?_ }
  · intro i
    let oldI : Fin (ell + 1) := deleteBelowLastIndex ell m hm i
    have hBefore :
        deleteTypeCoordinate m (ell + 2) (by omega)
          (some i.castSucc) = some oldI.castSucc :=
      deleteTypeCoordinate_before_last ell m hm i
    change Q.eRelation
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (some i.castSucc))
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (some (Fin.last ell))) =
      decide (i.val < deleteAtCut m f)
    rw [hBefore, hLast, hValid.oldToNewE oldI]
    exact congrArg decide (deleteAt_lt_iff_lt_deleteAtCut m f i.val)
  · intro i
    let oldI : Fin (ell + 1) := deleteBelowLastIndex ell m hm i
    have hBefore :
        deleteTypeCoordinate m (ell + 2) (by omega)
          (some i.castSucc) = some oldI.castSucc :=
      deleteTypeCoordinate_before_last ell m hm i
    change Q.eRelation
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (some (Fin.last ell)))
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (some i.castSucc)) = false
    rw [hBefore, hLast]
    exact hValid.newToOldE oldI
  · intro i hi r
    let oldI : Fin (ell + 1) := deleteBelowLastIndex ell m hm i
    have hBefore :
        deleteTypeCoordinate m (ell + 2) (by omega)
          (some i.castSucc) = some oldI.castSucc :=
      deleteTypeCoordinate_before_last ell m hm i
    have hBound : f ≤ oldI.val := by
      change f ≤ deleteAt m i.val
      by_contra h
      have hh : deleteAt m i.val < f := by omega
      have hShort : i.val < deleteAtCut m f :=
        (deleteAt_lt_iff_lt_deleteAtCut m f i.val).mp hh
      omega
    have hOld := hValid.noNewBinaryBeyondCut oldI hBound r
    change
      Q.lReduct.binary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (some i.castSucc))
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (some (Fin.last ell))) r = false ∧
      Q.lReduct.binary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (some (Fin.last ell)))
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (some i.castSucc)) r = false
    rw [hBefore, hLast]
    exact hOld

end SuccessorTree.V10
