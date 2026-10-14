import SuccessorTree.V10.CanonicalCrossing
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# Unique reconstruction of a one-level complete partial type

The genuine partial-type successor must be uniquely reconstructible
from its predecessor, canonical parameter and terminal Sigma letter.
This module proves the exact finite L+ extensionality step without
assuming S2 as an axiom.

One-level complete records have an old initial-socle prefix and a
last-column table containing every new directed binary and E pair
(including the type vertex t), together with new unary/diagonal bits.
Equality of those two pieces implies equality of the entire L+ type,
including false relation bits.

The next bridge is to replace the full last-column table with the
actual canonical empty/singleton parameter and Sigma letter, using
the proved no-new-tuples property of CanonicalCrossing. This module
does not falsely assert that every arbitrary column is admissible.
-/

namespace SuccessorTree.V10

/-- A complete last-column record over the predecessor's vertices,
the freshly added ordinary vertex and the distinguished type vertex.
It is deliberately redundant (both row and column retain the
new-new pair), but has no unconstrained 'additional' tuples. -/
structure CompleteNextColumn (ell db du dd : Nat) where
  toNew : Option (Fin (ell + 1)) → Fin db → Bool
  fromNew : Option (Fin (ell + 1)) → Fin db → Bool
  eToNew : Option (Fin (ell + 1)) → Bool
  eFromNew : Option (Fin (ell + 1)) → Bool
  unaryNew : Fin du → Bool
  diagonalNew : Fin dd → Bool

/-- Extract all atomic information introduced by the last ordinary
vertex at level ell. -/
def PartialTypeWithE.nextColumn
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd) :
    CompleteNextColumn ell db du dd :=
  { toNew := fun x r => Q.lReduct.binary x (some (Fin.last ell)) r
    fromNew := fun x r => Q.lReduct.binary (some (Fin.last ell)) x r
    eToNew := fun x => Q.eRelation x (some (Fin.last ell))
    eFromNew := fun x => Q.eRelation (some (Fin.last ell)) x
    unaryNew := Q.lReduct.unary (some (Fin.last ell))
    diagonalNew := Q.lReduct.diagonal (some (Fin.last ell)) }

/-- Equality of one-step predecessor and complete new column gives
equality of the entire L+ type. This proves the literal unique
atomic reconstruction required by S2, *conditional* only on the
column later being encoded by the actual parameter and Sigma letter. -/
theorem completeNextColumn_determines_type
    {ell db du dd : Nat}
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (hOld : Q.restrict (Nat.le_succ ell) =
      R.restrict (Nat.le_succ ell))
    (hNew : Q.nextColumn = R.nextColumn) :
    Q = R := by
  have hOldB (a b : Option (Fin ell)) (r : Fin db) :
      Q.lReduct.binary (liftTypeCoordinate (Nat.le_succ ell) a)
          (liftTypeCoordinate (Nat.le_succ ell) b) r =
      R.lReduct.binary (liftTypeCoordinate (Nat.le_succ ell) a)
          (liftTypeCoordinate (Nat.le_succ ell) b) r := by
    have h := congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.lReduct.binary a b r) hOld
    exact h
  have hOldU (a : Option (Fin ell)) (r : Fin du) :
      Q.lReduct.unary (liftTypeCoordinate (Nat.le_succ ell) a) r =
      R.lReduct.unary (liftTypeCoordinate (Nat.le_succ ell) a) r := by
    exact congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.lReduct.unary a r) hOld
  have hOldD (a : Option (Fin ell)) (r : Fin dd) :
      Q.lReduct.diagonal (liftTypeCoordinate (Nat.le_succ ell) a) r =
      R.lReduct.diagonal (liftTypeCoordinate (Nat.le_succ ell) a) r := by
    exact congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.lReduct.diagonal a r) hOld
  have hOldE (a b : Option (Fin ell)) :
      Q.eRelation (liftTypeCoordinate (Nat.le_succ ell) a)
          (liftTypeCoordinate (Nat.le_succ ell) b) =
      R.eRelation (liftTypeCoordinate (Nat.le_succ ell) a)
          (liftTypeCoordinate (Nat.le_succ ell) b) := by
    exact congrArg
      (fun T : PartialTypeWithE ell db du dd => T.eRelation a b) hOld
  have hToNew (a : Option (Fin (ell + 1))) (r : Fin db) :
      Q.lReduct.binary a (some (Fin.last ell)) r =
      R.lReduct.binary a (some (Fin.last ell)) r := by
    exact congrArg
      (fun C : CompleteNextColumn ell db du dd => C.toNew a r) hNew
  have hFromNew (a : Option (Fin (ell + 1))) (r : Fin db) :
      Q.lReduct.binary (some (Fin.last ell)) a r =
      R.lReduct.binary (some (Fin.last ell)) a r := by
    exact congrArg
      (fun C : CompleteNextColumn ell db du dd => C.fromNew a r) hNew
  have hEToNew (a : Option (Fin (ell + 1))) :
      Q.eRelation a (some (Fin.last ell)) =
      R.eRelation a (some (Fin.last ell)) := by
    exact congrArg
      (fun C : CompleteNextColumn ell db du dd => C.eToNew a) hNew
  have hEFromNew (a : Option (Fin (ell + 1))) :
      Q.eRelation (some (Fin.last ell)) a =
      R.eRelation (some (Fin.last ell)) a := by
    exact congrArg
      (fun C : CompleteNextColumn ell db du dd => C.eFromNew a) hNew
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      cases b with
      | none =>
        cases a with
        | none => exact hOldB none none r
        | some a =>
          induction a using Fin.lastCases with
          | last => exact hFromNew none r
          | cast a => exact hOldB (some a) none r
      | some b =>
        induction b using Fin.lastCases with
        | last => exact hToNew a r
        | cast b =>
          cases a with
          | none => exact hOldB none (some b) r
          | some a =>
            induction a using Fin.lastCases with
            | last => exact hFromNew (some b.castSucc) r
            | cast a => exact hOldB (some a) (some b) r
    · intro a r
      cases a with
      | none => exact hOldU none r
      | some a =>
        induction a using Fin.lastCases with
        | last =>
          exact congrArg
            (fun C : CompleteNextColumn ell db du dd => C.unaryNew r) hNew
        | cast a => exact hOldU (some a) r
    · intro a r
      cases a with
      | none => exact hOldD none r
      | some a =>
        induction a using Fin.lastCases with
        | last =>
          exact congrArg
            (fun C : CompleteNextColumn ell db du dd => C.diagonalNew r) hNew
        | cast a => exact hOldD (some a) r
  · intro a b
    cases b with
    | none =>
      cases a with
      | none => exact hOldE none none
      | some a =>
        induction a using Fin.lastCases with
        | last => exact hEFromNew none
        | cast a => exact hOldE (some a) none
    | some b =>
      induction b using Fin.lastCases with
      | last => exact hEToNew a
      | cast b =>
        cases a with
        | none => exact hOldE none (some b)
        | some a =>
          induction a using Fin.lastCases with
          | last => exact hEFromNew (some b.castSucc)
          | cast a => exact hOldE (some a) (some b)

end SuccessorTree.V10
