import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# S2 finite-record uniqueness from predecessor, parameter and Sigma letter

This module packages the last purely finite relational step in the
uniqueness proof for Definition 6.30. For two complete level-(ell+1)
L+ records with the same predecessor, suppose their newly introduced
ordinary vertices have the same free E cut f, the same complete
shortened parameter type through f and the same two-vertex terminal
Sigma letter.

If their E columns have exactly this free cut and the no-new-tuples
property holds above it, then the complete final atomic columns are
equal, and hence the two successors are exactly equal.

All of the hypotheses follow for records extracted from actual
partial structures by the already checked spacing, E3 and exact
parameter/letter extraction lemmas. The remaining paper-specific S2
interface is the equality of the free cut and canonical parameter
for the *forward* successor operation, and its S3 surjectivity onto
all covers of admissible Kpt nodes. No S2 axiom is used here.
-/

namespace SuccessorTree.V10

/-- Equality of all fields of a complete new-vertex column gives
literal equality of columns. -/
theorem CompleteNextColumn.eq_of_fields
    {ell db du dd : Nat}
    {C D : CompleteNextColumn ell db du dd}
    (hTo : C.toNew = D.toNew)
    (hFrom : C.fromNew = D.fromNew)
    (hETo : C.eToNew = D.eToNew)
    (hEFrom : C.eFromNew = D.eFromNew)
    (hUnary : C.unaryNew = D.unaryNew)
    (hDiag : C.diagonalNew = D.diagonalNew) :
    C = D := by
  cases C with
  | mk to0 from0 eTo0 eFrom0 unary0 diag0 =>
    cases D with
    | mk to1 from1 eTo1 eFrom1 unary1 diag1 =>
      cases hTo
      cases hFrom
      cases hETo
      cases hEFrom
      cases hUnary
      cases hDiag
      rfl

/-- Valid one-level E/free-cut and no-new-tuples columns, as forced by
Definition 6.28(1)--(3) for an ordinary new vertex. -/
structure ValidNewOrdinaryColumn
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) where
  oldToNewE : ∀ i : Fin ell,
    Q.eRelation (some i.castSucc) (some (Fin.last ell)) =
      decide (i.val < f)
  newToOldE : ∀ i : Fin ell,
    Q.eRelation (some (Fin.last ell)) (some i.castSucc) = false
  noNewBinaryBeyondCut : ∀ i : Fin ell,
    f ≤ i.val → ∀ r : Fin db,
      Q.lReduct.binary (some i.castSucc)
          (some (Fin.last ell)) r = false ∧
      Q.lReduct.binary (some (Fin.last ell))
          (some i.castSucc) r = false

/-- Literal terminal Sigma letter and canonical shortened parameter
determine every last-column bit once both complete types satisfy
the same free-cut/no-new-tuples conditions. -/
theorem nextColumn_eq_of_parameter_and_letter
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell)
    (hQ : ValidNewOrdinaryColumn Q f)
    (hR : ValidNewOrdinaryColumn R f)
    (hParameter : Q.lastOrdinaryParameter f hf =
      R.lastOrdinaryParameter f hf)
    (hLetter : Q.terminalLetter = R.terminalLetter) :
    Q.nextColumn = R.nextColumn := by
  let last : Fin (ell + 1) := Fin.last ell
  have hTerminalTo (r : Fin db) :
      Q.lReduct.binary none (some last) r =
      R.lReduct.binary none (some last) r := by
    have h := congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.lReduct.binary none (some 0) r) hLetter
    exact h
  have hTerminalFrom (r : Fin db) :
      Q.lReduct.binary (some last) none r =
      R.lReduct.binary (some last) none r := by
    have h := congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.lReduct.binary (some 0) none r) hLetter
    exact h
  have hTerminalSelf (r : Fin db) :
      Q.lReduct.binary (some last) (some last) r =
      R.lReduct.binary (some last) (some last) r := by
    exact congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.lReduct.binary (some 0) (some 0) r) hLetter
  have hTerminalETo :
      Q.eRelation none (some last) =
      R.eRelation none (some last) := by
    exact congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.eRelation none (some 0)) hLetter
  have hTerminalEFrom :
      Q.eRelation (some last) none =
      R.eRelation (some last) none := by
    exact congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.eRelation (some 0) none) hLetter
  have hTerminalESelf :
      Q.eRelation (some last) (some last) =
      R.eRelation (some last) (some last) := by
    exact congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.eRelation (some 0) (some 0)) hLetter
  have hTerminalUnary (r : Fin du) :
      Q.lReduct.unary (some last) r =
      R.lReduct.unary (some last) r := by
    exact congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.lReduct.unary (some 0) r) hLetter
  have hTerminalDiag (r : Fin dd) :
      Q.lReduct.diagonal (some last) r =
      R.lReduct.diagonal (some last) r := by
    exact congrArg
      (fun T : PartialTypeWithE 1 db du dd =>
        T.lReduct.diagonal (some 0) r) hLetter
  have hLowForward (i : Fin ell) (hi : i.val < f)
      (r : Fin db) :
      Q.lReduct.binary (some i.castSucc) (some last) r =
      R.lReduct.binary (some i.castSucc) (some last) r := by
    have h := congrArg
      (fun T : PartialTypeWithE f db du dd =>
        T.lReduct.binary (some ⟨i.val, hi⟩) none r) hParameter
    exact h
  have hLowBackward (i : Fin ell) (hi : i.val < f)
      (r : Fin db) :
      Q.lReduct.binary (some last) (some i.castSucc) r =
      R.lReduct.binary (some last) (some i.castSucc) r := by
    have h := congrArg
      (fun T : PartialTypeWithE f db du dd =>
        T.lReduct.binary none (some ⟨i.val, hi⟩) r) hParameter
    exact h
  have hEveryForward (i : Fin ell) (r : Fin db) :
      Q.lReduct.binary (some i.castSucc) (some last) r =
      R.lReduct.binary (some i.castSucc) (some last) r := by
    by_cases hi : i.val < f
    · exact hLowForward i hi r
    · have hle : f ≤ i.val := by omega
      exact (hQ.noNewBinaryBeyondCut i hle r).1.trans
        (hR.noNewBinaryBeyondCut i hle r).1.symm
  have hEveryBackward (i : Fin ell) (r : Fin db) :
      Q.lReduct.binary (some last) (some i.castSucc) r =
      R.lReduct.binary (some last) (some i.castSucc) r := by
    by_cases hi : i.val < f
    · exact hLowBackward i hi r
    · have hle : f ≤ i.val := by omega
      exact (hQ.noNewBinaryBeyondCut i hle r).2.trans
        (hR.noNewBinaryBeyondCut i hle r).2.symm
  have hTo (x : Option (Fin (ell + 1))) (r : Fin db) :
      Q.nextColumn.toNew x r = R.nextColumn.toNew x r := by
    cases x with
    | none => exact hTerminalTo r
    | some x =>
      induction x using Fin.lastCases with
      | last => exact hTerminalSelf r
      | cast i => exact hEveryForward i r
  have hFrom (x : Option (Fin (ell + 1))) (r : Fin db) :
      Q.nextColumn.fromNew x r = R.nextColumn.fromNew x r := by
    cases x with
    | none => exact hTerminalFrom r
    | some x =>
      induction x using Fin.lastCases with
      | last => exact hTerminalSelf r
      | cast i => exact hEveryBackward i r
  have hETo (x : Option (Fin (ell + 1))) :
      Q.nextColumn.eToNew x = R.nextColumn.eToNew x := by
    cases x with
    | none => exact hTerminalETo
    | some x =>
      induction x using Fin.lastCases with
      | last => exact hTerminalESelf
      | cast i => exact (hQ.oldToNewE i).trans (hR.oldToNewE i).symm
  have hEFrom (x : Option (Fin (ell + 1))) :
      Q.nextColumn.eFromNew x = R.nextColumn.eFromNew x := by
    cases x with
    | none => exact hTerminalEFrom
    | some x =>
      induction x using Fin.lastCases with
      | last => exact hTerminalESelf
      | cast i => exact (hQ.newToOldE i).trans (hR.newToOldE i).symm
  apply CompleteNextColumn.eq_of_fields
  · funext x r
    exact hTo x r
  · funext x r
    exact hFrom x r
  · funext x
    exact hETo x
  · funext x
    exact hEFrom x
  · funext r
    exact hTerminalUnary r
  · funext r
    exact hTerminalDiag r

/-- The finite L+ S2 uniqueness theorem in its precise geometric
form. The predecessor, shortened parameter, terminal letter and
shared E/free-cut conditions uniquely determine the complete
successor record, including every negative relation bit. -/
theorem complete_successor_unique_of_canonical_inputs
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (f : Nat) (hf : f ≤ ell)
    (hOld : Q.restrict (Nat.le_succ ell) =
      R.restrict (Nat.le_succ ell))
    (hQ : ValidNewOrdinaryColumn Q f)
    (hR : ValidNewOrdinaryColumn R f)
    (hParameter : Q.lastOrdinaryParameter f hf =
      R.lastOrdinaryParameter f hf)
    (hLetter : Q.terminalLetter = R.terminalLetter) :
    Q = R := by
  exact completeNextColumn_determines_type Q R hOld
    (nextColumn_eq_of_parameter_and_letter Q R f hf
      hQ hR hParameter hLetter)

end SuccessorTree.V10
