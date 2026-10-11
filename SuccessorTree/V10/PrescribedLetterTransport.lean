import SuccessorTree.V10.PrescribedPrefixCore
import SuccessorTree.V10.PrescribedETransport
import Mathlib.Tactic

/-!
# Complete terminal-letter transport through a prescribed insertion

The actual finite prescribed constructor copies every old L atom and
every old E pair under the increasing address insertion. The terminal
Sigma letter is a complete one-vertex L+ type, so it is unchanged for
any retained ordinary vertex and any retained distinguished vertex.

No assumption on the inserted ordinary column beyond the constructor's
existing validity is needed. In particular the column may be non-neutral.
This is a finite transport lemma, not a weak successor theorem.
-/

namespace SuccessorTree.V10

/-- Complete terminal-letter equality between source and inserted target
for an old ordinary coordinate and an old type vertex. In particular E
remains part of the letter; L-only agreement is not enough. -/
theorem prescribedInsertPartial_terminalLetter_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (Q : PartialTypeWithE (ell+1) db du dd)
    (k : Nat) (hValid : ValidNewOrdinaryColumn Q k)
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool)
    (n v : Nat) (hn : n < A.size) (hv : v < A.size) :
    ((prescribedInsertPartial A Q k hValid hell hellPos hk hGate upperIncoming upperOutgoing).partialTypeAt
      (insertAddress ell n + 1) (insertAddress ell v)).terminalLetter =
    (A.partialTypeAt (n + 1) v).terminalLetter := by
  let B := prescribedInsertPartial A Q k hValid hell hellPos hk hGate upperIncoming upperOutgoing
  have hIns : IsLInsertion A B ell :=
    prescribedInsertPartial_isLInsertion A Q k hValid hell hellPos hk hGate upperIncoming upperOutgoing
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      cases x with
      | none =>
        cases y with
        | none =>
          change B.L.binary (insertAddress ell v) (insertAddress ell v) r =
            A.L.binary v v r
          exact hIns.binary v v hv hv r
        | some y =>
          have hy : y = 0 := Fin.eq_zero y
          subst y
          change B.L.binary (insertAddress ell v) (insertAddress ell n) r =
            A.L.binary v n r
          exact hIns.binary v n hv hn r
      | some x =>
        have hx : x = 0 := Fin.eq_zero x
        subst x
        cases y with
        | none =>
          change B.L.binary (insertAddress ell n) (insertAddress ell v) r =
            A.L.binary n v r
          exact hIns.binary n v hn hv r
        | some y =>
          have hy : y = 0 := Fin.eq_zero y
          subst y
          change B.L.binary (insertAddress ell n) (insertAddress ell n) r =
            A.L.binary n n r
          exact hIns.binary n n hn hn r
    · intro x r
      cases x with
      | none =>
        change B.L.unary (insertAddress ell v) r = A.L.unary v r
        exact hIns.unary v hv r
      | some x =>
        have hx : x = 0 := Fin.eq_zero x
        subst x
        change B.L.unary (insertAddress ell n) r = A.L.unary n r
        exact hIns.unary n hn r
    · intro x r
      cases x with
      | none =>
        change B.L.diagonal (insertAddress ell v) r = A.L.diagonal v r
        exact hIns.diagonal v hv r
      | some x =>
        have hx : x = 0 := Fin.eq_zero x
        subst x
        change B.L.diagonal (insertAddress ell n) r = A.L.diagonal n r
        exact hIns.diagonal n hn r
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        change B.E (insertAddress ell v) (insertAddress ell v) = A.E v v
        exact insertE_old_pair_eq A ell k hell hellPos v v hv hv
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change B.E (insertAddress ell v) (insertAddress ell n) = A.E v n
        exact insertE_old_pair_eq A ell k hell hellPos v n hv hn
    | some x =>
      have hx : x = 0 := Fin.eq_zero x
      subst x
      cases y with
      | none =>
        change B.E (insertAddress ell n) (insertAddress ell v) = A.E n v
        exact insertE_old_pair_eq A ell k hell hellPos n v hn hv
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change B.E (insertAddress ell n) (insertAddress ell n) = A.E n n
        exact insertE_old_pair_eq A ell k hell hellPos n n hn hn

end SuccessorTree.V10
