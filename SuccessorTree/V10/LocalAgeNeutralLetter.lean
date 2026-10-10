import SuccessorTree.V10.LocalAgeNeutralInjective
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# The genuine canonical terminal Sigma letter is invariant under neutral insertion

For an original ordinary vertex n and a type vertex v, a neutral insertion
of a new ordinary coordinate at ell shifts both n and v by the same explicit
increasing address map. Every directed L atom and every auxiliary E atom of
this old pair is copied exactly, as are unary and diagonal singleton facts.

Consequently the FULL level-one terminal Sigma letter of the corresponding
canonical successor is literally unchanged, on EVERY source level: below,
at, and above the inserted gap. This is the letter component required by
weak successor preservation of the total neutralKptSkip map.

The parameter component and existence of the target successor with the
mapped parameter are separate obligations.
-/

namespace SuccessorTree.V10

/-- Complete terminal-letter equality between source and inserted target
for an old ordinary coordinate and an old type vertex. In particular E
remains part of the letter; L-only agreement is not enough. -/
theorem neutralInsert_terminalLetter_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (n v : Nat) (hn : n < A.size) (hv : v < A.size) :
    ((neutralInsert A ell hell hellPos).partialTypeAt
      (insertAddress ell n + 1) (insertAddress ell v)).terminalLetter =
    (A.partialTypeAt (n + 1) v).terminalLetter := by
  let B := neutralInsert A ell hell hellPos
  have hIns : IsLInsertion A B ell :=
    neutralInsert_isLInsertion A ell hell hellPos
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
        exact neutralInsert_old_E_eq A ell hell hellPos v v hv hv
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change B.E (insertAddress ell v) (insertAddress ell n) = A.E v n
        exact neutralInsert_old_E_eq A ell hell hellPos v n hv hn
    | some x =>
      have hx : x = 0 := Fin.eq_zero x
      subst x
      cases y with
      | none =>
        change B.E (insertAddress ell n) (insertAddress ell v) = A.E n v
        exact neutralInsert_old_E_eq A ell hell hellPos n v hn hv
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change B.E (insertAddress ell n) (insertAddress ell n) = A.E n n
        exact neutralInsert_old_E_eq A ell hell hellPos n n hn hn

end SuccessorTree.V10
