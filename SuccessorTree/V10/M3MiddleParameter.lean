import SuccessorTree.V10.M3MiddleLetter
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# The real M3 clone repeats the old canonical shortened parameter

The newly inserted ordinary coordinate ell has free level
d=freeLevel_A(n). Its complete L+ type through this cut is exactly
the old ordinary coordinate n's type through the same cut, including
all directed L atoms, present/absent E atoms, and singleton data.

Therefore the canonical parameter list of the successor at ell
equals that of the earlier n-th crossing of the distinguished type
vertex. At d=0 both lists are genuinely empty; no spurious level-zero
parameter appears.

This is a concrete finite-model comparison; the global M3 successor
construction and choice independence remain separate.
-/

namespace SuccessorTree.V10

/-- Complete equality of the newly inserted ordinary vertex's type
at d=fl_A(n) with the older ordinary vertex n's type at the same
cut. Both E and L parts are checked atom by atom. -/
theorem middleCloneInsertPartial_new_parameter_type
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell) :
    let d := A.freeLevel n
    (middleCloneInsertPartial A ell n hell hn).partialTypeAt d ell =
      A.partialTypeAt d n := by
  let B := middleCloneInsertPartial A ell n hell hn
  let d := A.freeLevel n
  let D := middleCloneInsertedLData A ell n
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
  have hL : B.L = insertL A ell D := rfl
  have hd : d ≤ n := A.freeLevel_le n
  have hdd : d < ell := lt_of_le_of_lt hd hn
  have hNSize : n < A.size := lt_of_lt_of_le hn hell
  have hCutB : d ≤ B.freeLevel ell := by
    rw [middleCloneInsertPartial_new_freeLevel A ell n hell hn]
  have hBelow (i : Fin d) : i.val < ell :=
    lt_trans i.isLt hdd
  have hOldAddress (i : Fin d) : insertAddress ell i.val = i.val :=
    insertAddress_below ell i.val (hBelow i)
  have hNewUnary (r : Fin du) : B.L.unary ell r = A.L.unary n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hNewDiagonal (r : Fin dd) :
      B.L.diagonal ell r = A.L.diagonal n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hNewLoop (r : Fin db) :
      B.L.binary ell ell r = A.L.binary n n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hOut (i : Fin d) (r : Fin db) :
      B.L.binary ell i.val r = A.L.binary n i.val r := by
    rw [hL]
    have hi := hBelow i
    have hdi : i.val < A.freeLevel n := i.isLt
    simp [insertL, D, middleCloneInsertedLData, removeInserted,
      hi, hdi, Nat.ne_of_lt hi]
  have hIn (i : Fin d) (r : Fin db) :
      B.L.binary i.val ell r = A.L.binary i.val n r := by
    rw [hL]
    have hi := hBelow i
    have hdi : i.val < A.freeLevel n := i.isLt
    simp [insertL, D, middleCloneInsertedLData, removeInserted,
      hi, hdi, Nat.ne_of_lt hi]
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      cases x with
      | none =>
        cases y with
        | none =>
          change B.L.binary ell ell r = A.L.binary n n r
          exact hNewLoop r
        | some j =>
          change B.L.binary ell j.val r = A.L.binary n j.val r
          exact hOut j r
      | some i =>
        cases y with
        | none =>
          change B.L.binary i.val ell r = A.L.binary i.val n r
          exact hIn i r
        | some j =>
          change B.L.binary i.val j.val r = A.L.binary i.val j.val r
          have hh := hIns.binary i.val j.val
            (lt_of_lt_of_le (hBelow i) hell)
            (lt_of_lt_of_le (hBelow j) hell) r
          rw [hOldAddress i,hOldAddress j] at hh
          exact hh
    · intro x r
      cases x with
      | none =>
          change B.L.unary ell r = A.L.unary n r
          exact hNewUnary r
      | some i =>
          change B.L.unary i.val r = A.L.unary i.val r
          have hh := hIns.unary i.val
            (lt_of_lt_of_le (hBelow i) hell) r
          rw [hOldAddress i] at hh
          exact hh
    · intro x r
      cases x with
      | none =>
          change B.L.diagonal ell r = A.L.diagonal n r
          exact hNewDiagonal r
      | some i =>
          change B.L.diagonal i.val r = A.L.diagonal i.val r
          have hh := hIns.diagonal i.val
            (lt_of_lt_of_le (hBelow i) hell) r
          rw [hOldAddress i] at hh
          exact hh
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        calc
          (B.partialTypeAt d ell).eRelation none none = false :=
            B.partialTypeAt_no_typeE_loop d ell
          _ = (A.partialTypeAt d n).eRelation none none :=
            (A.partialTypeAt_no_typeE_loop d n).symm
      | some j =>
        calc
          (B.partialTypeAt d ell).eRelation none (some j) = false :=
            B.partialTypeAt_no_reverseE d ell hCutB j
          _ = (A.partialTypeAt d n).eRelation none (some j) :=
            (A.partialTypeAt_no_reverseE d n (le_refl d) j).symm
    | some i =>
      cases y with
      | none =>
        calc
          (B.partialTypeAt d ell).eRelation (some i) none = true :=
            B.partialTypeAt_fullESocle d ell hCutB i
          _ = (A.partialTypeAt d n).eRelation (some i) none :=
            (A.partialTypeAt_fullESocle d n (le_refl d) i).symm
      | some j =>
        change B.E i.val j.val = A.E i.val j.val
        rw [middleCloneInsertPartial_E_eq A ell n hell hn]
        have hh := insertE_old_pair_eq A ell d hell (by omega)
          i.val j.val
          (lt_of_lt_of_le (hBelow i) hell)
          (lt_of_lt_of_le (hBelow j) hell)
        rw [hOldAddress i,hOldAddress j] at hh
        exact hh

/-- The new successor carries EXACTLY the earlier crossing's
canonical empty-or-positive-singleton parameter list. This uses the
real complete L+ parameter records, not only the L-reduct. -/
theorem middleCloneInsertPartial_parameterList_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) :
    let B := middleCloneInsertPartial A ell n hell hn
    let d := A.freeLevel n
    ((B.partialTypeAt (ell+1) (insertAddress ell v)).canonicalParameterRecord
      d ((A.freeLevel_le n).trans (Nat.le_of_lt hn))).toList =
    ((A.partialTypeAt (n+1) v).canonicalParameterRecord
      d (A.freeLevel_le n)).toList := by
  let B := middleCloneInsertPartial A ell n hell hn
  let d := A.freeLevel n
  have hd : d ≤ n := A.freeLevel_le n
  have hdEll : d ≤ ell := hd.trans (Nat.le_of_lt hn)
  have hNew := partialTypeAt_lastOrdinaryParameter B
    (insertAddress ell v) ell d hdEll
  have hOld := partialTypeAt_lastOrdinaryParameter A
    v n d hd
  have hClone := middleCloneInsertPartial_new_parameter_type
    A ell n hell hn
  have hParam :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).lastOrdinaryParameter
        d hdEll =
      (A.partialTypeAt (n+1) v).lastOrdinaryParameter d hd := by
    calc
      (B.partialTypeAt (ell+1) (insertAddress ell v)).lastOrdinaryParameter
          d hdEll = B.partialTypeAt d ell := hNew
      _ = A.partialTypeAt d n := hClone
      _ = (A.partialTypeAt (n+1) v).lastOrdinaryParameter d hd :=
        hOld.symm
  by_cases hz : d = 0
  · simp [PartialTypeWithE.canonicalParameterRecord, hz]
  · simp [PartialTypeWithE.canonicalParameterRecord, hz, hParam]

end SuccessorTree.V10
