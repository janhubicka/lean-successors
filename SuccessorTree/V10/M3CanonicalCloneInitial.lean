import SuccessorTree.V10.M3CanonicalCloneParameter
import Mathlib.Tactic

/-!
# The full ordinary clone socle follows from canonical M3 successor data

Suppose Q extends T by one ordinary coordinate ell, uses the same
terminal Sigma letter as T's earlier crossing at n<ell, and gives
the newly inserted coordinate the earlier vertex n's canonical free
cut d. For positive d, the canonical parameter is the full earlier
parameter; when d=0 there is no parameter. In both cases the valid
new E column forces absence of all L-links beyond d.

This proves exactly the lower atomic clone data needed for the
finite-L corrected B3 reduction. The special zero-parameter case
does NOT require equality of artificial level-zero parameters.
-/

namespace SuccessorTree.V10

/-- Entire initial L-socle of Q is an honest duplicate of the
earlier coordinate n, with the original positive free cut d.
The parameter equation is needed only when d is positive. -/
theorem m3_initial_clone_of_canonical_records
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (n d : Nat) (hn : n < ell) (hd : d ≤ n)
    (hOld : Q.restrict (Nat.le_succ ell) = T)
    (hLetter : Q.terminalLetter = earlierTerminalLetter T n hn)
    (hParam : 0 < d →
      Q.lastOrdinaryParameter d (hd.trans (Nat.le_of_lt hn)) =
        earlierOrdinaryParameter T n d hn hd)
    (hValid : ValidNewOrdinaryColumn Q d) :
    MiddleCloneInitialL (prescribedOrdinarySocle Q) n ell d := by
  have hSingle :=
    m3_terminalLetter_copies_singleton T Q n hn hOld hLetter
  have hnLe : n ≤ ell := Nat.le_of_lt hn
  have hLast : (Fin.last ell : Fin (ell+1)) =
      (⟨ell, Nat.lt_succ_self ell⟩ : Fin (ell+1)) :=
    Fin.ext rfl
  refine {
    n_before := hn
    cut_le_source := hd
    source_in_carrier := ?_
    same_unary := ?_
    same_diagonal := ?_
    no_lower_links := ?_
    copy_lower := ?_ }
  · change n ≤ ell
    exact hnLe
  · intro t
    simpa [prescribedOrdinarySocle, hnLe, hLast] using hSingle.1 t
  · intro t
    simpa [prescribedOrdinarySocle, hnLe, hLast] using hSingle.2 t
  · intro x hdx hxe t
    let xi : Fin ell := ⟨x, hxe⟩
    have hnolink :=
      m3_valid_no_lower_links_past_cut Q d hValid xi hdx t
    have hxl : x ≤ ell := Nat.le_of_lt hxe
    constructor
    · have h : (prescribedOrdinarySocle Q).binary ell x t =
          Q.lReduct.binary (some (Fin.last ell))
            (some xi.castSucc) t := by
        simp [prescribedOrdinarySocle, hxl, xi, hLast]
      exact h.trans hnolink.1
    · have h : (prescribedOrdinarySocle Q).binary x ell t =
          Q.lReduct.binary (some xi.castSucc)
            (some (Fin.last ell)) t := by
        simp [prescribedOrdinarySocle, hxl, xi, hLast]
      exact h.trans hnolink.2
  · intro x hx t
    let i : Fin d := ⟨x, hx⟩
    have hPos : 0 < d := by omega
    have hp := m3_parameter_copies_lower_pairs
      T Q n d hn hd hOld (hParam hPos) i t
    have hxell : x < ell := lt_trans hx (lt_of_le_of_lt hd hn)
    have hxl : x ≤ ell := Nat.le_of_lt hxell
    have hA : (prescribedOrdinarySocle Q).binary ell x t =
      Q.lReduct.binary (some (Fin.last ell))
        (some (⟨x, by omega⟩ : Fin (ell+1))) t := by
      simp [prescribedOrdinarySocle, hxl, hLast]
    have hB : (prescribedOrdinarySocle Q).binary n x t =
      Q.lReduct.binary (some (⟨n, by omega⟩ : Fin (ell+1)))
        (some (⟨x, by omega⟩ : Fin (ell+1))) t := by
      simp [prescribedOrdinarySocle, hnLe, hxl]
    have hC : (prescribedOrdinarySocle Q).binary x ell t =
      Q.lReduct.binary (some (⟨x, by omega⟩ : Fin (ell+1)))
        (some (Fin.last ell)) t := by
      simp [prescribedOrdinarySocle, hxl, hLast]
    have hD : (prescribedOrdinarySocle Q).binary x n t =
      Q.lReduct.binary (some (⟨x, by omega⟩ : Fin (ell+1)))
        (some (⟨n, by omega⟩ : Fin (ell+1))) t := by
      simp [prescribedOrdinarySocle, hxl, hnLe]
    exact ⟨hA.trans (hp.1.trans hB.symm),
      hC.trans (hp.2.trans hD.symm)⟩

end SuccessorTree.V10
