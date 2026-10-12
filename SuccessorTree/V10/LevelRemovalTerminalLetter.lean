import SuccessorTree.V10.LevelRemovalAdmissibleType
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# Deleting an earlier ordinary coordinate preserves the terminal L+ letter

For a complete successor record with two or more ordinary socle vertices,
remove an ordinary coordinate m strictly before the LAST original ordinary
vertex. The last remaining ordinary vertex is the old last vertex, simply
renumbered down by one. Thus the full two-vertex terminal Sigma letter
(on that vertex and the distinguished type vertex) is unchanged.

This includes both directed positive and absent binary tuples, all
unary/diagonal bits and every E pair. We prove the equality on arbitrary
complete L+ records, then transfer it to the actual guarded finite
partial-structure deletion.

This is a prerequisite to the ABOVE-GAP weak successor case in M2, but does
not assert that the parameter record or canonical successor law survives
deletion. No M2 hypothesis or corrected B3 age condition is added.
-/

namespace SuccessorTree.V10

/-- Skipping m and then selecting the LAST retained ordinary vertex
is the same as selecting the old last ordinary vertex. The distinguished
type vertex is unchanged. -/
theorem deleteTypeCoordinate_terminal
    (ell m : Nat) (hm : m < ell + 1)
    (a : Option (Fin 1)) :
    deleteTypeCoordinate m (ell + 2) (by omega)
        (terminalCoordinate ell a) =
      terminalCoordinate (ell + 1) a := by
  cases a with
  | none => rfl
  | some i =>
      apply congrArg some
      apply Fin.ext
      have hAddr : deleteAt m (ell + 1 - 1) = ell + 1 := by
        rw [deleteAt_above m (ell + 1 - 1) (by omega)]
        omega
      simpa [deleteTypeCoordinate, deletedSocleCoordinate,
        terminalCoordinate] using hAddr

/-- The terminal complete L+ letter does not change if an earlier
ordinary coordinate is removed from its predecessor socle. -/
theorem PartialTypeWithE.deleteOrdinary_terminalLetter
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 2) db du dd)
    (m : Nat) (hm : m < ell + 1) :
    (Q.deleteOrdinary m (by omega)).terminalLetter =
      Q.terminalLetter := by
  have hCoord (a : Option (Fin 1)) :
      deleteTypeCoordinate m (ell + 2) (by omega)
          (terminalCoordinate ell a) =
        terminalCoordinate (ell + 1) a :=
    deleteTypeCoordinate_terminal ell m hm a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change Q.lReduct.binary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (terminalCoordinate ell a))
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (terminalCoordinate ell b)) r =
        Q.lReduct.binary
          (terminalCoordinate (ell + 1) a)
          (terminalCoordinate (ell + 1) b) r
      rw [hCoord a,hCoord b]
    · intro a r
      change Q.lReduct.unary
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (terminalCoordinate ell a)) r =
        Q.lReduct.unary (terminalCoordinate (ell + 1) a) r
      rw [hCoord a]
    · intro a r
      change Q.lReduct.diagonal
          (deleteTypeCoordinate m (ell + 2) (by omega)
            (terminalCoordinate ell a)) r =
        Q.lReduct.diagonal (terminalCoordinate (ell + 1) a) r
      rw [hCoord a]
  · intro a b
    change Q.eRelation
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (terminalCoordinate ell a))
        (deleteTypeCoordinate m (ell + 2) (by omega)
          (terminalCoordinate ell b)) =
      Q.eRelation
        (terminalCoordinate (ell + 1) a)
        (terminalCoordinate (ell + 1) b)
    rw [hCoord a,hCoord b]

/-- For an actual guarded finite partial structure, the extracted
terminal letter after coordinate deletion is the unchanged old letter
of the retained distinguished vertex. -/
theorem deleteAtPartial_terminalLetter_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m ell v : Nat)
    (hnext : m + 1 < A.size)
    (hguard : A.freeLevel (m + 1) < m)
    (hm : m < ell + 1)
    (hv : ell + 2 ≤ A.freeLevel v) :
    ((deleteAtPartial A m hnext hguard).partialTypeAt
        (ell + 1) (v - 1)).terminalLetter =
      (A.partialTypeAt (ell + 2) v).terminalLetter := by
  have hmv : m < v := by
    have hFl : A.freeLevel v ≤ v := A.freeLevel_le v
    omega
  have hAddr : deleteAt m (v - 1) = v :=
    deleteAt_pred_of_gt m v hmv
  have hRecords :=
    deleteAtPartial_partialTypeAt_eq_deleteOrdinary
      A m (ell + 2) (v - 1) hnext hguard (by omega)
  rw [hAddr] at hRecords
  have hRecords' :
      (deleteAtPartial A m hnext hguard).partialTypeAt
        (ell + 1) (v - 1) =
      (A.partialTypeAt (ell + 2) v).deleteOrdinary m (by omega) := by
    simpa [Nat.add_assoc] using hRecords
  rw [hRecords']
  exact PartialTypeWithE.deleteOrdinary_terminalLetter
    (A.partialTypeAt (ell + 2) v) m hm

end SuccessorTree.V10
