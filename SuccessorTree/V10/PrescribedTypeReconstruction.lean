import SuccessorTree.V10.PrescribedBoringData
import SuccessorTree.V10.CompleteNextColumn
import Mathlib.Tactic

/-!
# Exact upper L-type reconstruction from predecessor and inserted column

The remaining B3 input in Lemma 6.51 requires the *complete* L-type of
each upper vertex through ell+1, not merely its relations to the newly
inserted ordinary vertex.

A relational (no E) type at ell+1 is determined uniquely by:
1. its complete predecessor over the first ell coordinates and t;
2. the entire last ordinary binary row and column, including its loop,
   directed links to t, and all absent links;
3. the last ordinary vertex's unary and diagonal data.

The proof is an atomic extensionality argument using the actual Fin.last
decomposition. It ensures there is no missing off-diagonal orientation
or negative atom in later B3 matching arguments.
-/

namespace SuccessorTree.V10

/-- Complete reconstruction of an L-type at level ell+1 from the old
predecessor, new directed row/column, and singleton data. Every Boolean
relation value is compared, positive AND absent, with no symmetry axiom. -/
theorem relationalPrefix_eq_of_predecessor_last
    {ell db du dd : Nat}
    (Q R : RelationalPrefixType (ell + 1) db du dd)
    (hOld : Q.restrict (Nat.le_succ ell) =
      R.restrict (Nat.le_succ ell))
    (hTo : ∀ x : Option (Fin (ell + 1)), ∀ t : Fin db,
      Q.binary x (some (Fin.last ell)) t =
      R.binary x (some (Fin.last ell)) t)
    (hFrom : ∀ x : Option (Fin (ell + 1)), ∀ t : Fin db,
      Q.binary (some (Fin.last ell)) x t =
      R.binary (some (Fin.last ell)) x t)
    (hUnary : ∀ t : Fin du,
      Q.unary (some (Fin.last ell)) t =
      R.unary (some (Fin.last ell)) t)
    (hDiagonal : ∀ t : Fin dd,
      Q.diagonal (some (Fin.last ell)) t =
      R.diagonal (some (Fin.last ell)) t) :
    Q = R := by
  have hOldB (x y : Option (Fin ell)) (t : Fin db) :
      Q.binary (liftTypeCoordinate (Nat.le_succ ell) x)
          (liftTypeCoordinate (Nat.le_succ ell) y) t =
      R.binary (liftTypeCoordinate (Nat.le_succ ell) x)
          (liftTypeCoordinate (Nat.le_succ ell) y) t :=
    congrArg (fun T : RelationalPrefixType ell db du dd =>
      T.binary x y t) hOld
  have hOldU (x : Option (Fin ell)) (t : Fin du) :
      Q.unary (liftTypeCoordinate (Nat.le_succ ell) x) t =
      R.unary (liftTypeCoordinate (Nat.le_succ ell) x) t :=
    congrArg (fun T : RelationalPrefixType ell db du dd =>
      T.unary x t) hOld
  have hOldD (x : Option (Fin ell)) (t : Fin dd) :
      Q.diagonal (liftTypeCoordinate (Nat.le_succ ell) x) t =
      R.diagonal (liftTypeCoordinate (Nat.le_succ ell) x) t :=
    congrArg (fun T : RelationalPrefixType ell db du dd =>
      T.diagonal x t) hOld
  apply RelationalPrefixType.eq_of_atoms
  · intro a b t
    cases b with
    | none =>
      cases a with
      | none => exact hOldB none none t
      | some a =>
        induction a using Fin.lastCases with
        | last => exact hFrom none t
        | cast a => exact hOldB (some a) none t
    | some b =>
      induction b using Fin.lastCases with
      | last => exact hTo a t
      | cast b =>
        cases a with
        | none => exact hOldB none (some b) t
        | some a =>
          induction a using Fin.lastCases with
          | last => exact hFrom (some b.castSucc) t
          | cast a => exact hOldB (some a) (some b) t
  · intro a t
    cases a with
    | none => exact hOldU none t
    | some a =>
      induction a using Fin.lastCases with
      | last => exact hUnary t
      | cast a => exact hOldU (some a) t
  · intro a t
    cases a with
    | none => exact hOldD none t
    | some a =>
      induction a using Fin.lastCases with
      | last => exact hDiagonal t
      | cast a => exact hOldD (some a) t

end SuccessorTree.V10
