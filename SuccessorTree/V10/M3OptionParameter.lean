import SuccessorTree.V10.M3RecordB3
import SuccessorTree.V10.EmptyParameterS2
import Mathlib.Tactic

/-!
# Read the duplicated free cut from the actual canonical parameter list

In the canonical M3 successor, the input parameter is an empty list
when the copied old vertex n has free cut zero, otherwise the exact
singleton shortened type of that vertex. Unlike an artificial
level-zero parameter, this is precisely the canonical S-tree API.

Equality of the option-parameter lists forces equality of the two
free cuts, even for the empty case. At a positive cut it also gives
equality of the shortened parameter records. Combining this with the
valid new column and repeated terminal letter supplies the entire
initial middle-clone L column.

The only remaining M3 bridge is to connect these exact parameter and
letter lists with the prescribed values of the concrete forward
canonicalKptSucc; no extra abstract function axiom is needed here.
-/

namespace SuccessorTree.V10

/-- Option.toList loses no information, including in the empty case. -/
private theorem option_eq_of_toList_eq {α : Type*}
    (a b : Option α) (h : a.toList = b.toList) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Equal canonical lists force the SAME earlier vertex free cut.
The proof checks both the empty and positive singleton cases rather
than assuming the list contains a parameter. -/
theorem m3_canonical_parameter_list_cut_eq
    {ell k db du dd : Nat}
    (Q : PartialTypeWithE (ell+1) db du dd)
    (R : PartialTypeWithE (k+1) db du dd)
    (f d : Nat) (hf : f ≤ ell) (hd : d ≤ k)
    (hList : (Q.canonicalParameterRecord f hf).toList =
      (R.canonicalParameterRecord d hd).toList) :
    f = d := by
  have hOpt := option_eq_of_toList_eq
    (Q.canonicalParameterRecord f hf)
    (R.canonicalParameterRecord d hd) hList
  by_cases hfz : f = 0
  · by_cases hdz : d = 0
    · omega
    · simp [PartialTypeWithE.canonicalParameterRecord,
        hfz, hdz] at hOpt
  · by_cases hdz : d = 0
    · simp [PartialTypeWithE.canonicalParameterRecord,
        hfz, hdz] at hOpt
    · have hRaw :
          (⟨f,Q.lastOrdinaryParameter f hf⟩ :
            RawPartialTypeNode db du dd) =
          (⟨d,R.lastOrdinaryParameter d hd⟩ :
            RawPartialTypeNode db du dd) := by
        simpa [PartialTypeWithE.canonicalParameterRecord,
          hfz, hdz] using hOpt
      exact congrArg Sigma.fst hRaw

/-- Equality of the genuine canonical successor parameter lists and
terminal letters suffices for the complete ordinary M3 clone column.
At positive cut the list fixes the full parameter record; at cut zero
there is no positive lower coordinate and thus no parameter premise. -/
theorem m3_initial_clone_of_canonical_parameter_lists
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (n d f : Nat) (hn : n < ell) (hd : d ≤ n)
    (hf : f ≤ ell)
    (hOld : Q.restrict (Nat.le_succ ell) = T)
    (hLetter : Q.terminalLetter = earlierTerminalLetter T n hn)
    (hValid : ValidNewOrdinaryColumn Q f)
    (hList : (Q.canonicalParameterRecord f hf).toList =
      ((T.restrict (Nat.succ_le_of_lt hn)).canonicalParameterRecord d hd).toList) :
    MiddleCloneInitialL (prescribedOrdinarySocle Q) n ell d := by
  have hCut : f = d :=
    m3_canonical_parameter_list_cut_eq
      Q (T.restrict (Nat.succ_le_of_lt hn)) f d hf hd hList
  subst f
  have hOpt := option_eq_of_toList_eq
    (Q.canonicalParameterRecord d hf)
    ((T.restrict (Nat.succ_le_of_lt hn)).canonicalParameterRecord d hd)
    hList
  have hPar : 0 < d →
      Q.lastOrdinaryParameter d (hd.trans (Nat.le_of_lt hn)) =
        earlierOrdinaryParameter T n d hn hd := by
    intro hp
    have hz : d ≠ 0 := Nat.ne_of_gt hp
    have hRaw :
        (⟨d, Q.lastOrdinaryParameter d hf⟩ :
          RawPartialTypeNode db du dd) =
        (⟨d,(T.restrict (Nat.succ_le_of_lt hn)).lastOrdinaryParameter d hd⟩ :
          RawPartialTypeNode db du dd) := by
      simpa [PartialTypeWithE.canonicalParameterRecord, hz] using hOpt
    have hRecord :
        Q.lastOrdinaryParameter d hf =
          (T.restrict (Nat.succ_le_of_lt hn)).lastOrdinaryParameter d hd := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
    simpa only [earlierOrdinaryParameter] using hRecord
  exact m3_initial_clone_of_canonical_records T Q
    n d hn hd hOld hLetter hPar hValid

end SuccessorTree.V10
