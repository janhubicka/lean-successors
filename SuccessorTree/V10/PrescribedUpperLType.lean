import SuccessorTree.V10.PrescribedTypeReconstruction
import Mathlib.Tactic

/-!
# Realizing an actual prescribed upper L-type in an inserted finite model

The three-clause age test used by Lemma 6.51 needs the complete induced
L-type of every linked upper vertex through the INSERTED coordinate.

This file proves the precise local bridge. Suppose the given prescribed
one-step output Q has predecessor equal to the original upper vertex's
type through ell (B1), the single inserted vertex's ordinary lower column
equals Q's, and its two directed L-relations to the upper vertex equal
Q's terminal letter. Then the actual inserted L model realizes EXACTLY
Q's entire L-reduct at that upper vertex through ell+1. This includes
all binary tuples and their nonrelations, both orientations, loops,
unary and diagonal facts.

No E equality is imposed on a forbidden L-age witness. The separate
PrescribedInsertPartial module controls E on the actual partial structure.
The next bridge must derive the lower/terminal premises uniformly from f.
-/

namespace SuccessorTree.V10

/-- All L-atoms contributed by one inserted ordinary vertex ell agree with
the given complete prescribed target Q, including the terminal pair with
the particular old upper vertex u. -/
def InsertedLData.MatchesPrescribedUpper
    {db du dd ell : Nat}
    (D : InsertedLData db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (u : Nat) : Prop :=
  (∀ t : Fin db,
    D.loop t =
      Q.lReduct.binary (some (Fin.last ell)) (some (Fin.last ell)) t) ∧
  (∀ t : Fin du,
    D.unary t = Q.lReduct.unary (some (Fin.last ell)) t) ∧
  (∀ t : Fin dd,
    D.diagonal t = Q.lReduct.diagonal (some (Fin.last ell)) t) ∧
  (∀ i : Fin ell, ∀ t : Fin db,
    D.incoming i.val t =
      Q.lReduct.binary (some i.castSucc) (some (Fin.last ell)) t) ∧
  (∀ i : Fin ell, ∀ t : Fin db,
    D.outgoing i.val t =
      Q.lReduct.binary (some (Fin.last ell)) (some i.castSucc) t) ∧
  (∀ t : Fin db,
    D.incoming u t = Q.lReduct.binary none (some (Fin.last ell)) t) ∧
  (∀ t : Fin db,
    D.outgoing u t = Q.lReduct.binary (some (Fin.last ell)) none t)

/-- The old predecessor of a shifted upper vertex is its exact original
L-type over the old ell coordinates. Here no E or upper-column
hypotheses are needed; it follows just from old-atom transport. -/
theorem insertL_upper_predecessor_eq
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (D : InsertedLData db du dd)
    (u : Nat)
    (hu : ell ≤ u) :
    (RelationalPrefixType.ofAgeModel (insertL A ell D)
      (ell + 1) (insertAddress ell u)).restrict
      (Nat.le_succ ell) =
    (A.partialTypeAt ell u).lReduct := by
  have hBelow : ∀ i : Fin ell,
      insertAddress ell i.val = i.val :=
    fun i => insertAddress_below ell i.val i.isLt
  apply RelationalPrefixType.eq_of_atoms
  · intro a b t
    cases a with
    | none =>
      cases b with
      | none =>
        change (insertL A ell D).binary (insertAddress ell u)
            (insertAddress ell u) t = A.L.binary u u t
        exact insertL_old_binary A ell D u u t
      | some j =>
        change (insertL A ell D).binary (insertAddress ell u) j.val t =
          A.L.binary u j.val t
        simpa only [hBelow j] using
          (insertL_old_binary A ell D u j.val t)
    | some i =>
      cases b with
      | none =>
        change (insertL A ell D).binary i.val (insertAddress ell u) t =
          A.L.binary i.val u t
        simpa only [hBelow i] using
          (insertL_old_binary A ell D i.val u t)
      | some j =>
        change (insertL A ell D).binary i.val j.val t =
          A.L.binary i.val j.val t
        simpa only [hBelow i, hBelow j] using
          (insertL_old_binary A ell D i.val j.val t)
  · intro a t
    cases a with
    | none =>
      change (insertL A ell D).unary (insertAddress ell u) t =
        A.L.unary u t
      exact insertL_old_unary A ell D u t
    | some i =>
      change (insertL A ell D).unary i.val t =
        A.L.unary i.val t
      simpa only [hBelow i] using
        (insertL_old_unary A ell D i.val t)
  · intro a t
    cases a with
    | none =>
      change (insertL A ell D).diagonal (insertAddress ell u) t =
        A.L.diagonal u t
      exact insertL_old_diagonal A ell D u t
    | some i =>
      change (insertL A ell D).diagonal i.val t =
        A.L.diagonal i.val t
      simpa only [hBelow i] using
        (insertL_old_diagonal A ell D i.val t)

/-- All prescribed one-level L-types are realized exactly when their
complete predecessor and last ordinary column are copied. -/
theorem insertL_realizes_prescribed_upper_L_type
    {db du dd ell : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (D : InsertedLData db du dd)
    (u : Nat) (hu : ell ≤ u)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hOld : Q.lReduct.restrict (Nat.le_succ ell) =
      (A.partialTypeAt ell u).lReduct)
    (hNew : D.MatchesPrescribedUpper Q u) :
    RelationalPrefixType.ofAgeModel (insertL A ell D)
      (ell + 1) (insertAddress ell u) = Q.lReduct := by
  let R := RelationalPrefixType.ofAgeModel (insertL A ell D)
    (ell + 1) (insertAddress ell u)
  have hPred : R.restrict (Nat.le_succ ell) =
      Q.lReduct.restrict (Nat.le_succ ell) := by
    exact (insertL_upper_predecessor_eq A D u hu).trans hOld.symm
  have hNewAddr : insertAddress ell u ≠ ell := by
    rw [insertAddress_above ell u hu]
    omega
  have hOldBelow : ∀ i : Fin ell, i.val < ell := fun i => i.isLt
  have hTo : ∀ x : Option (Fin (ell + 1)), ∀ t : Fin db,
      R.binary x (some (Fin.last ell)) t =
        Q.lReduct.binary x (some (Fin.last ell)) t := by
    intro x t
    cases x with
    | none =>
      change (insertL A ell D).binary (insertAddress ell u) ell t =
        Q.lReduct.binary none (some (Fin.last ell)) t
      simpa [insertL, hNewAddr] using hNew.2.2.2.2.2.1 t
    | some x =>
      induction x using Fin.lastCases with
      | last =>
        change (insertL A ell D).binary ell ell t =
          Q.lReduct.binary (some (Fin.last ell)) (some (Fin.last ell)) t
        simpa [insertL] using hNew.1 t
      | cast i =>
        change (insertL A ell D).binary i.val ell t =
          Q.lReduct.binary (some i.castSucc) (some (Fin.last ell)) t
        have hi : i.val ≠ ell := by omega
        simpa [insertL, hi, removeInserted, i.isLt] using hNew.2.2.2.1 i t
  have hFrom : ∀ x : Option (Fin (ell + 1)), ∀ t : Fin db,
      R.binary (some (Fin.last ell)) x t =
        Q.lReduct.binary (some (Fin.last ell)) x t := by
    intro x t
    cases x with
    | none =>
      change (insertL A ell D).binary ell (insertAddress ell u) t =
        Q.lReduct.binary (some (Fin.last ell)) none t
      simpa [insertL, hNewAddr, removeInserted_insertAddress] using
        hNew.2.2.2.2.2.2 t
    | some x =>
      induction x using Fin.lastCases with
      | last =>
        change (insertL A ell D).binary ell ell t =
          Q.lReduct.binary (some (Fin.last ell)) (some (Fin.last ell)) t
        simpa [insertL] using hNew.1 t
      | cast i =>
        change (insertL A ell D).binary ell i.val t =
          Q.lReduct.binary (some (Fin.last ell)) (some i.castSucc) t
        have hi : i.val ≠ ell := by omega
        simpa [insertL, hi, removeInserted, i.isLt] using
          hNew.2.2.2.2.1 i t
  have hUnary : ∀ t : Fin du,
      R.unary (some (Fin.last ell)) t =
        Q.lReduct.unary (some (Fin.last ell)) t := by
    intro t
    change (insertL A ell D).unary ell t =
      Q.lReduct.unary (some (Fin.last ell)) t
    simpa [insertL] using hNew.2.1 t
  have hDiagonal : ∀ t : Fin dd,
      R.diagonal (some (Fin.last ell)) t =
        Q.lReduct.diagonal (some (Fin.last ell)) t := by
    intro t
    change (insertL A ell D).diagonal ell t =
      Q.lReduct.diagonal (some (Fin.last ell)) t
    simpa [insertL] using hNew.2.2.1 t
  exact relationalPrefix_eq_of_predecessor_last R Q.lReduct
    hPred hTo hFrom hUnary hDiagonal

end SuccessorTree.V10
