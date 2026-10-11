import SuccessorTree.V10.M3LinkedProjection
import Mathlib.Tactic

/-!
# The actual gated M3 insertion satisfies exactly the LINKED clone data

The original free E cut of an upper old vertex can lie before ell.
In that case the concrete M3 constructor suppresses BOTH directed
relations to the newly inserted clone; copying all upper L atoms
unconditionally would contradict E3.

For upper vertices genuinely linked to the clone, the gate is forced
open. The old L atoms at n and at every retained coordinate are
preserved. This proves the linked-only projection premise from the
actual finite constructor, with no age, E-witness, or extra
upper-copying assumption.
-/

namespace SuccessorTree.V10

/-- The literal middle clone is a linked-only L-clone of the old n.
There are no further assumptions on the source A besides the
genuine finite structure and its valid coordinate bounds. -/
theorem middleCloneInsertPartial_linkedLData
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell) :
    MiddleCloneLinkedLData
      (middleCloneInsertPartial A ell n hell hn).L
      n ell (A.freeLevel n) := by
  let B := middleCloneInsertPartial A ell n hell hn
  let D := middleCloneInsertedLData A ell n
  have hL : B.L = insertL A ell D := rfl
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
  have hnOld : n < A.size := lt_of_lt_of_le hn hell
  have hnEq : insertAddress ell n = n :=
    insertAddress_below ell n hn
  have hOldUnary (r : Fin du) : B.L.unary n r = A.L.unary n r := by
    have h := hIns.unary n hnOld r
    rw [hnEq] at h
    exact h
  have hOldDiagonal (r : Fin dd) :
      B.L.diagonal n r = A.L.diagonal n r := by
    have h := hIns.diagonal n hnOld r
    rw [hnEq] at h
    exact h
  have hNewUnary (r : Fin du) : B.L.unary ell r = A.L.unary n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hNewDiagonal (r : Fin dd) :
      B.L.diagonal ell r = A.L.diagonal n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hBelowOut (x : Nat) (hx : x < ell) (r : Fin db) :
      B.L.binary ell x r =
        (if x < A.freeLevel n then A.L.binary n x r else false) := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData, removeInserted, hx,
      Nat.ne_of_lt hx]
  have hBelowIn (x : Nat) (hx : x < ell) (r : Fin db) :
      B.L.binary x ell r =
        (if x < A.freeLevel n then A.L.binary x n r else false) := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData, removeInserted, hx,
      Nat.ne_of_lt hx]
  refine {
    n_before := hn
    cut_before_source := A.freeLevel_le n
    source_in_carrier := ?_
    same_unary := ?_
    same_diagonal := ?_
    no_lower_links := ?_
    copy_lower := ?_
    copy_upper_linked := ?_ }
  · exact (B.carrier_iff n).2 (by
      have hs := hIns.size_eq
      omega)
  · intro r
    exact (hNewUnary r).trans (hOldUnary r).symm
  · intro r
    exact (hNewDiagonal r).trans (hOldDiagonal r).symm
  · intro x hdx hx r
    have hnot : ¬ x < A.freeLevel n := Nat.not_lt.mpr hdx
    constructor
    · rw [hBelowOut x hx r, if_neg hnot]
    · rw [hBelowIn x hx r, if_neg hnot]
  · intro x hx r
    have hxe : x < ell :=
      lt_trans hx (lt_of_le_of_lt (A.freeLevel_le n) hn)
    have hxOld : x < A.size := lt_of_lt_of_le hxe hell
    have hxEq : insertAddress ell x = x :=
      insertAddress_below ell x hxe
    have hCopyOut : B.L.binary n x r = A.L.binary n x r := by
      have hh := hIns.binary n x hnOld hxOld r
      rw [hnEq, hxEq] at hh
      exact hh
    have hCopyIn : B.L.binary x n r = A.L.binary x n r := by
      have hh := hIns.binary x n hxOld hnOld r
      rw [hnEq, hxEq] at hh
      exact hh
    constructor
    · rw [hBelowOut x hxe r, if_pos hx]
      exact hCopyOut.symm
    · rw [hBelowIn x hxe r, if_pos hx]
      exact hCopyIn.symm
  · intro x hx hxe hLinked r
    have hSize : x < B.size :=
      (B.carrier_iff x).1 hx
    let u := x - 1
    have huLower : ell ≤ u := by
      dsimp [u]
      omega
    have huSize : u < A.size := by
      have hs := hIns.size_eq
      dsimp [u]
      omega
    have hAddr : insertAddress ell u = x := by
      rw [insertAddress_above ell u huLower]
      dsimp [u]
      omega
    have huNot : ¬ u < ell := Nat.not_lt.mpr huLower
    have hUpperOut (t : Fin db) :
        B.L.binary ell x t =
          (if ell ≤ A.freeLevel u then A.L.binary n u t else false) := by
      rw [hL]
      simp [insertL, D, middleCloneInsertedLData, removeInserted,
        Nat.ne_of_gt hxe, Nat.not_lt.mpr (Nat.le_of_lt hxe),
        huNot, u]
    have hUpperIn (t : Fin db) :
        B.L.binary x ell t =
          (if ell ≤ A.freeLevel u then A.L.binary u n t else false) := by
      rw [hL]
      simp [insertL, D, middleCloneInsertedLData, removeInserted,
        Nat.ne_of_gt hxe, Nat.not_lt.mpr (Nat.le_of_lt hxe),
        huNot, u]
    have hGate : ell ≤ A.freeLevel u := by
      by_contra hnot
      have hOutFalse (t : Fin db) : B.L.binary ell x t = false := by
        rw [hUpperOut t, if_neg hnot]
      have hInFalse (t : Fin db) : B.L.binary x ell t = false := by
        rw [hUpperIn t, if_neg hnot]
      obtain ⟨t, ht⟩ := hLinked
      rcases ht with ht | ht
      · rw [hOutFalse t] at ht
        cases ht
      · rw [hInFalse t] at ht
        cases ht
    have hOldOut : B.L.binary n x r = A.L.binary n u r := by
      have hh := hIns.binary n u hnOld huSize r
      rw [hnEq, hAddr] at hh
      exact hh
    have hOldIn : B.L.binary x n r = A.L.binary u n r := by
      have hh := hIns.binary u n huSize hnOld r
      rw [hnEq, hAddr] at hh
      exact hh
    constructor
    · rw [hUpperOut r, if_pos hGate]
      exact hOldOut.symm
    · rw [hUpperIn r, if_pos hGate]
      exact hOldIn.symm

end SuccessorTree.V10
