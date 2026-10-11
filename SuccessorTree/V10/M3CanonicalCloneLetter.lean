import SuccessorTree.V10.M3CorrectedB3Reduction
import SuccessorTree.V10.ExtractSuccessorComponents
import Mathlib.Tactic

/-!
# Canonical M3 duplication: terminal-letter part of the clone identities

Let T be a complete level-ell source record and Q its one-level
successor. Fix an earlier ordinary coordinate n<ell. If Q restricts
to T and has the same actual terminal Sigma letter as the earlier
source crossing T|_(n+1), the newly inserted ordinary vertex ell
has exactly the same unary and diagonal singleton data as n, and
its two directed relations to the distinguished type vertex equal
those of the old n. These facts are proved directly from complete
record restriction and terminal letter, not assumed as clone axioms.

No age argument or E restriction on L-witnesses is used. The remaining
ordinary lower column identities require canonical parameter transport.
-/

namespace SuccessorTree.V10

/-- The terminal letter of the earlier n crossing, extracted from a
longer complete level-ell type, is the canonical two-vertex letter
that the proposed M3 successor repeats at its new coordinate ell. -/
def earlierTerminalLetter
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (n : Nat) (hn : n < ell) :
    PartialTypeWithE 1 db du dd :=
  (T.restrict (Nat.succ_le_of_lt hn)).terminalLetter

/-- The actual new terminal letter and the old source record
determine the two complete directed L-pairs from ell to t by equality
with the existing coordinate n. The equivalence covers false atoms. -/
theorem m3_terminalLetter_copies_upper_pairs
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (n : Nat) (hn : n < ell)
    (hOld : Q.restrict (Nat.le_succ ell) = T)
    (hLetter : Q.terminalLetter = earlierTerminalLetter T n hn)
    (t : Fin db) :
    Q.lReduct.binary (some (Fin.last ell)) none t =
      Q.lReduct.binary (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) none t ∧
    Q.lReduct.binary none (some (Fin.last ell)) t =
      Q.lReduct.binary none
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t := by
  let i : Fin ell := ⟨n, hn⟩
  let j : Fin (ell+1) := ⟨n, Nat.lt_succ_of_lt hn⟩
  have hLetterForward := congrArg
    (fun R : PartialTypeWithE 1 db du dd =>
      R.lReduct.binary (some 0) none t) hLetter
  have hLetterBackward := congrArg
    (fun R : PartialTypeWithE 1 db du dd =>
      R.lReduct.binary none (some 0) t) hLetter
  have hOldForward := congrArg
    (fun R : PartialTypeWithE ell db du dd =>
      R.lReduct.binary (some i) none t) hOld
  have hOldBackward := congrArg
    (fun R : PartialTypeWithE ell db du dd =>
      R.lReduct.binary none (some i) t) hOld
  change Q.lReduct.binary (some (Fin.last ell)) none t =
    T.lReduct.binary (some i) none t at hLetterForward
  change Q.lReduct.binary none (some (Fin.last ell)) t =
    T.lReduct.binary none (some i) t at hLetterBackward
  change Q.lReduct.binary (some j) none t =
    T.lReduct.binary (some i) none t at hOldForward
  change Q.lReduct.binary none (some j) t =
    T.lReduct.binary none (some i) t at hOldBackward
  exact ⟨hLetterForward.trans hOldForward.symm,
    hLetterBackward.trans hOldBackward.symm⟩

/-- Repeating a canonical terminal letter duplicates the entire
singleton L-label of n at the new ordinary vertex ell. Both unary
predicates and binary diagonals are retained separately. -/
theorem m3_terminalLetter_copies_singleton
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (n : Nat) (hn : n < ell)
    (hOld : Q.restrict (Nat.le_succ ell) = T)
    (hLetter : Q.terminalLetter = earlierTerminalLetter T n hn) :
    (∀ t : Fin du,
      Q.lReduct.unary (some (Fin.last ell)) t =
        Q.lReduct.unary
          (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t) ∧
    (∀ t : Fin dd,
      Q.lReduct.diagonal (some (Fin.last ell)) t =
        Q.lReduct.diagonal
          (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t) := by
  let i : Fin ell := ⟨n,hn⟩
  let j : Fin (ell+1) := ⟨n,Nat.lt_succ_of_lt hn⟩
  constructor
  · intro t
    have hNew := congrArg
      (fun R : PartialTypeWithE 1 db du dd =>
        R.lReduct.unary (some 0) t) hLetter
    have hOrig := congrArg
      (fun R : PartialTypeWithE ell db du dd =>
        R.lReduct.unary (some i) t) hOld
    change Q.lReduct.unary (some (Fin.last ell)) t =
      T.lReduct.unary (some i) t at hNew
    change Q.lReduct.unary (some j) t =
      T.lReduct.unary (some i) t at hOrig
    exact hNew.trans hOrig.symm
  · intro t
    have hNew := congrArg
      (fun R : PartialTypeWithE 1 db du dd =>
        R.lReduct.diagonal (some 0) t) hLetter
    have hOrig := congrArg
      (fun R : PartialTypeWithE ell db du dd =>
        R.lReduct.diagonal (some i) t) hOld
    change Q.lReduct.diagonal (some (Fin.last ell)) t =
      T.lReduct.diagonal (some i) t at hNew
    change Q.lReduct.diagonal (some j) t =
      T.lReduct.diagonal (some i) t at hOrig
    exact hNew.trans hOrig.symm

end SuccessorTree.V10
