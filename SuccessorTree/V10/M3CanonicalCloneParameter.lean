
import SuccessorTree.V10.M3CanonicalCloneLetter
import SuccessorTree.V10.PrescribedCorrectedB3
import Mathlib.Tactic

/-!
# Canonical M3 lower parameter determines duplicate's lower L-pairs

Given a successor Q extending T, equality of its full shortened
parameter with the earlier n-th parameter of T forces the two directed
binary pairs to the inserted coordinate ell to be those of n at every
old coordinate x below the source free cut d. For x at or above d, the
valid E-cut forbids either directed binary link.
This is an L-only record calculation; the full M3 B3 bridge remains open.
-/

namespace SuccessorTree.V10

def earlierOrdinaryParameter
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (n d : Nat) (hn : n < ell) (hd : d ≤ n) :
    PartialTypeWithE d db du dd :=
  (T.restrict (Nat.succ_le_of_lt hn)).lastOrdinaryParameter d hd

theorem m3_parameter_copies_lower_pairs
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (n d : Nat) (hn : n < ell) (hd : d ≤ n)
    (hOld : Q.restrict (Nat.le_succ ell) = T)
    (hParameter :
      Q.lastOrdinaryParameter d (hd.trans (Nat.le_of_lt hn)) =
      earlierOrdinaryParameter T n d hn hd)
    (x : Fin d) (t : Fin db) :
    Q.lReduct.binary (some (Fin.last ell))
      (some (⟨x.val, Nat.lt_succ_of_lt
        (lt_of_lt_of_le x.isLt (hd.trans (Nat.le_of_lt hn)))⟩ :
        Fin (ell+1))) t =
      Q.lReduct.binary
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1)))
        (some (⟨x.val, Nat.lt_succ_of_lt
          (lt_of_lt_of_le x.isLt (hd.trans (Nat.le_of_lt hn)))⟩ :
          Fin (ell+1))) t ∧
    Q.lReduct.binary
      (some (⟨x.val, Nat.lt_succ_of_lt
        (lt_of_lt_of_le x.isLt (hd.trans (Nat.le_of_lt hn)))⟩ :
        Fin (ell+1))) (some (Fin.last ell)) t =
      Q.lReduct.binary
        (some (⟨x.val, Nat.lt_succ_of_lt
          (lt_of_lt_of_le x.isLt (hd.trans (Nat.le_of_lt hn)))⟩ :
          Fin (ell+1)))
        (some (⟨n, Nat.lt_succ_of_lt hn⟩ : Fin (ell+1))) t := by
  let ni : Fin ell := ⟨n,hn⟩
  let xi : Fin ell :=
    ⟨x.val,lt_of_lt_of_le x.isLt (hd.trans (Nat.le_of_lt hn))⟩
  have hpTo := congrArg
    (fun R : PartialTypeWithE d db du dd =>
      R.lReduct.binary none (some x) t) hParameter
  have hpFrom := congrArg
    (fun R : PartialTypeWithE d db du dd =>
      R.lReduct.binary (some x) none t) hParameter
  have hOldTo := congrArg
    (fun R : PartialTypeWithE ell db du dd =>
      R.lReduct.binary (some ni) (some xi) t) hOld
  have hOldFrom := congrArg
    (fun R : PartialTypeWithE ell db du dd =>
      R.lReduct.binary (some xi) (some ni) t) hOld
  change Q.lReduct.binary (some (Fin.last ell)) (some xi.castSucc) t =
    T.lReduct.binary (some ni) (some xi) t at hpTo
  change Q.lReduct.binary (some xi.castSucc) (some (Fin.last ell)) t =
    T.lReduct.binary (some xi) (some ni) t at hpFrom
  change Q.lReduct.binary (some ni.castSucc) (some xi.castSucc) t =
    T.lReduct.binary (some ni) (some xi) t at hOldTo
  change Q.lReduct.binary (some xi.castSucc) (some ni.castSucc) t =
    T.lReduct.binary (some xi) (some ni) t at hOldFrom
  exact ⟨hpTo.trans hOldTo.symm, hpFrom.trans hOldFrom.symm⟩

theorem m3_valid_no_lower_links_past_cut
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell+1) db du dd) (d : Nat)
    (hValid : ValidNewOrdinaryColumn Q d)
    (x : Fin ell) (h : d ≤ x.val) (t : Fin db) :
    Q.lReduct.binary (some (Fin.last ell)) (some x.castSucc) t = false ∧
    Q.lReduct.binary (some x.castSucc) (some (Fin.last ell)) t = false := by
  obtain ⟨a,b⟩ := hValid.noNewBinaryBeyondCut x h t
  exact ⟨b,a⟩

end SuccessorTree.V10
