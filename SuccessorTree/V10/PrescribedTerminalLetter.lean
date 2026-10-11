import SuccessorTree.V10.PrescribedKptFullPrefix
import SuccessorTree.V10.PrescribedETransport
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# Terminal Sigma letter transport for genuinely prescribed insertion

The canonical terminal letter of an actual Kpt successor records one
old ordinary coordinate n and the retained type vertex v, including
both directions of every L and E relation and their singleton facts.
An arbitrary non-neutral prescribed insertion at ell changes neither
old-old L atoms nor old-old E atoms. Hence this terminal letter is
LITERALLY unchanged for all n and v, at any position relative to ell.

This is an independent finite component of successor preservation.
Parameter-list transport and the global canonical successor equation
remain separate obligations.
-/

namespace SuccessorTree.V10

/-- Exact terminal Sigma-letter equality for every literal prescribed
insertion, including all old E pairs and absent directed L relations.
No compatibility or age assumption beyond the finite constructor
requirements is used. -/
theorem prescribedInsertPartial_terminalLetter_eq
    {ell db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (k : Nat) (hValid : ValidNewOrdinaryColumn Q k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (upperIn upperOut : Nat → Fin db → Bool)
    (n v : Nat) (hn : n < A.size) (hv : v < A.size) :
    ((prescribedInsertPartial A Q k hValid hell hPos hk hGate
      upperIn upperOut).partialTypeAt (insertAddress ell n+1)
      (insertAddress ell v)).terminalLetter =
    (A.partialTypeAt (n+1) v).terminalLetter := by
  let B := prescribedInsertPartial A Q k hValid hell hPos hk hGate
    upperIn upperOut
  have hIns : IsLInsertion A B ell :=
    prescribedInsertPartial_isLInsertion A Q k hValid hell
      hPos hk hGate upperIn upperOut
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
        exact insertE_old_pair_eq A ell k hell hPos v v hv hv
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change B.E (insertAddress ell v) (insertAddress ell n) = A.E v n
        exact insertE_old_pair_eq A ell k hell hPos v n hv hn
    | some x =>
      have hx : x = 0 := Fin.eq_zero x
      subst x
      cases y with
      | none =>
        change B.E (insertAddress ell n) (insertAddress ell v) = A.E n v
        exact insertE_old_pair_eq A ell k hell hPos n v hn hv
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change B.E (insertAddress ell n) (insertAddress ell n) = A.E n n
        exact insertE_old_pair_eq A ell k hell hPos n n hn hn

end SuccessorTree.V10
