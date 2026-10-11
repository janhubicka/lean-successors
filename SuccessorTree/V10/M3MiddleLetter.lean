import SuccessorTree.V10.M3MiddleTarget
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# The genuine middle-clone insertion repeats the earlier Sigma letter

For a distinguished vertex v with original E free cut ell and an old
coordinate n<ell, the inserted new ordinary vertex ell duplicates
the terminal L+ letter of the old pair (n,v): singleton fields,
both directed binary relations including false atoms, binary loops,
and all four auxiliary E pairs.

The E bits are not assumed to agree. The new E link ell->shift(v)
and the old link n->v are both forced by their genuine free cuts.
This is the finite Sigma-letter input used by M3 duplication.
-/

namespace SuccessorTree.V10

/-- Exact repetition of the old n-th crossing's complete terminal
Sigma-letter in the actual gated inserted finite L+ model. -/
theorem middleCloneInsertPartial_terminalLetter_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) (hv : v < A.size)
    (hOld : A.freeLevel v = ell) :
    ((middleCloneInsertPartial A ell n hell hn).partialTypeAt
        (ell+1) (insertAddress ell v)).terminalLetter =
      (A.partialTypeAt (n+1) v).terminalLetter := by
  let B := middleCloneInsertPartial A ell n hell hn
  let D := middleCloneInsertedLData A ell n
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
  have hL : B.L = insertL A ell D := rfl
  have hvGE : ell ≤ v := by
    have hh := A.freeLevel_le v
    omega
  have hNSize : n < A.size := lt_of_lt_of_le hn hell
  have hAddr : insertAddress ell v = v+1 :=
    insertAddress_above ell v hvGE
  have hAddrNE : insertAddress ell v ≠ ell := by
    rw [hAddr]
    omega
  have hFreeB : B.freeLevel (insertAddress ell v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      A ell n hell hn v hv hOld
  have hAboveB : ell+1 ≤ B.freeLevel (insertAddress ell v) := by
    rw [hFreeB]
  have hAboveA : n+1 ≤ A.freeLevel v := by omega
  have hNewTo (r : Fin db) :
      B.L.binary ell (insertAddress ell v) r = A.L.binary n v r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData,
      hAddrNE, removeInserted_insertAddress, hvGE, hOld]
  have hNewFrom (r : Fin db) :
      B.L.binary (insertAddress ell v) ell r = A.L.binary v n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData,
      hAddrNE, removeInserted_insertAddress, hvGE, hOld]
  have hNewLoop (r : Fin db) :
      B.L.binary ell ell r = A.L.binary n n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hNewUnary (r : Fin du) : B.L.unary ell r = A.L.unary n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hNewDiagonal (r : Fin dd) :
      B.L.diagonal ell r = A.L.diagonal n r := by
    rw [hL]
    simp [insertL, D, middleCloneInsertedLData]
  have hOldBinary (r : Fin db) :
      B.L.binary (insertAddress ell v) (insertAddress ell v) r =
        A.L.binary v v r :=
    hIns.binary v v hv hv r
  have hOldUnary (r : Fin du) :
      B.L.unary (insertAddress ell v) r = A.L.unary v r :=
    hIns.unary v hv r
  have hOldDiagonal (r : Fin dd) :
      B.L.diagonal (insertAddress ell v) r = A.L.diagonal v r :=
    hIns.diagonal v hv r
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      cases a with
      | none =>
        cases b with
        | none =>
          change B.L.binary (insertAddress ell v) (insertAddress ell v) r =
            A.L.binary v v r
          exact hOldBinary r
        | some b =>
          have hb : b = 0 := Fin.eq_zero b
          subst b
          change B.L.binary (insertAddress ell v) ell r =
            A.L.binary v n r
          exact hNewFrom r
      | some a =>
        have ha : a = 0 := Fin.eq_zero a
        subst a
        cases b with
        | none =>
          change B.L.binary ell (insertAddress ell v) r =
            A.L.binary n v r
          exact hNewTo r
        | some b =>
          have hb : b = 0 := Fin.eq_zero b
          subst b
          change B.L.binary ell ell r = A.L.binary n n r
          exact hNewLoop r
    · intro a r
      cases a with
      | none =>
        change B.L.unary (insertAddress ell v) r =
          A.L.unary v r
        exact hOldUnary r
      | some a =>
        have ha : a = 0 := Fin.eq_zero a
        subst a
        change B.L.unary ell r = A.L.unary n r
        exact hNewUnary r
    · intro a r
      cases a with
      | none =>
        change B.L.diagonal (insertAddress ell v) r =
          A.L.diagonal v r
        exact hOldDiagonal r
      | some a =>
        have ha : a = 0 := Fin.eq_zero a
        subst a
        change B.L.diagonal ell r = A.L.diagonal n r
        exact hNewDiagonal r
  · intro a b
    cases a with
    | none =>
      cases b with
      | none =>
        calc
          (B.partialTypeAt (ell+1) (insertAddress ell v)).terminalLetter.eRelation
              none none = false :=
            B.partialTypeAt_no_typeE_loop (ell+1) (insertAddress ell v)
          _ = (A.partialTypeAt (n+1) v).terminalLetter.eRelation none none :=
            (A.partialTypeAt_no_typeE_loop (n+1) v).symm
      | some b =>
        have hb : b = 0 := Fin.eq_zero b
        subst b
        change B.E (insertAddress ell v) ell = A.E v n
        exact
          (B.partialTypeAt_no_reverseE (ell+1) (insertAddress ell v)
            hAboveB (Fin.last ell)).trans
          (A.partialTypeAt_no_reverseE (n+1) v
            hAboveA (Fin.last n)).symm
    | some a =>
      have ha : a = 0 := Fin.eq_zero a
      subst a
      cases b with
      | none =>
        change B.E ell (insertAddress ell v) = A.E n v
        exact
          (B.partialTypeAt_fullESocle (ell+1) (insertAddress ell v)
            hAboveB (Fin.last ell)).trans
          (A.partialTypeAt_fullESocle (n+1) v
            hAboveA (Fin.last n)).symm
      | some b =>
        have hb : b = 0 := Fin.eq_zero b
        subst b
        change B.E ell ell = A.E n n
        have hNew : B.E ell ell = false := by
          rw [middleCloneInsertPartial_E_eq A ell n hell hn]
          exact insertE_new_loop_false A ell (A.freeLevel n)
            ((A.freeLevel_le n).trans (Nat.le_of_lt hn))
        have hOldLoop : A.E n n = false := by
          cases h : A.E n n with
          | false => rfl
          | true =>
              have hsp := A.spaced n n h
              omega
        exact hNew.trans hOldLoop.symm

end SuccessorTree.V10
