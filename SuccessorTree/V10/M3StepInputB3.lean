import SuccessorTree.V10.M3OptionParameter
import SuccessorTree.V10.M3VariableCutB3
import Mathlib.Tactic

/-!
# Same canonical one-step inputs imply corrected finite M3 B3

The actual M3 prescription takes the canonical empty-or-singleton
parameter list and terminal Sigma letter of the old crossing at n,
and uses those same inputs to form a new successor at ell>n.

This module proves the *finite record* implication. For each source
T, both the earlier record T|_(n+1) and the prescribed output f(T)
are genuine valid one-level columns sharing the same p and c. Their
free E cuts are not assumed equal: equality follows from the
empty/singleton parameter list. The complete lower clone column and
the upper clone pairs then follow from the checked finite record
lemmas, and the finite L-only projection yields corrected B3.

The final connection between this record interface and the concrete
`IsCanonicalKptStep` / `canonicalKptSucc` graph remains a separate
adapter. No E structure is imposed on corrected B3's finite
L-age witnesses, and the old n-th free cut may vary with T.
-/

namespace SuccessorTree.V10

/-- Literal one-step canonical input decomposition of a complete
record Q at level m+1: an actual valid new E/free cut, the canonical
empty-or-positive-singleton parameter list, and the full L+ terminal
Sigma letter. It is precisely the data carried by IsCanonicalKptStep,
but without the auxiliary admissible-node witness. -/
def HasCanonicalRecordInputs
    {m db du dd : Nat}
    (Q : PartialTypeWithE (m+1) db du dd)
    (p : List (RawPartialTypeNode db du dd))
    (c : PartialTypeWithE 1 db du dd) : Prop :=
  ∃ (f : Nat) (hf : f ≤ m),
    ValidNewOrdinaryColumn Q f ∧
    p = (Q.canonicalParameterRecord f hf).toList ∧
    c = Q.terminalLetter

/-- Sharing a canonical input list and terminal letter between the
previous crossing of T at n and the output f(T) at ell forces the
full corrected finite B3 no-age-change condition. All free cuts are
selected separately for each source T; no global d is postulated. -/
theorem PrescribedBoringData.correctedB3_of_repeated_canonical_inputs
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (hRepeat : ∀ T, T ∈ F.source →
      ∃ (p : List (RawPartialTypeNode db du dd))
        (c : PartialTypeWithE 1 db du dd),
        HasCanonicalRecordInputs
          (T.restrict (Nat.succ_le_of_lt hn)) p c ∧
        HasCanonicalRecordInputs (F.target T) p c) :
    F.CorrectedB3 family := by
  have hLetter : ∀ T, T ∈ F.source →
      (F.target T).terminalLetter = earlierTerminalLetter T n hn := by
    intro T hT
    obtain ⟨p,c,hEarlier,hLater⟩ := hRepeat T hT
    obtain ⟨d,hd,hValidOld,hParamOld,hLetterOld⟩ := hEarlier
    obtain ⟨f,hf,hValidNew,hParamNew,hLetterNew⟩ := hLater
    exact hLetterNew.symm.trans hLetterOld
  have hUpper : F.MiddleCloneUpperL n hn :=
    F.middleCloneUpperL_of_terminalLetter n hn hLetter
  have hLower : ∀ T, T ∈ F.source →
      ∃ d : Nat,
        MiddleCloneInitialL
          (prescribedOrdinarySocle (F.target T)) n ell d := by
    intro T hT
    obtain ⟨p,c,hEarlier,hLater⟩ := hRepeat T hT
    obtain ⟨d,hd,hValidOld,hParamOld,hLetterOld⟩ := hEarlier
    obtain ⟨f,hf,hValidNew,hParamNew,hLetterNew⟩ := hLater
    have hParamList :
        ((F.target T).canonicalParameterRecord f hf).toList =
          ((T.restrict (Nat.succ_le_of_lt hn)).canonicalParameterRecord d hd).toList :=
      hParamNew.symm.trans hParamOld
    have hLetterEq :
        (F.target T).terminalLetter = earlierTerminalLetter T n hn :=
      hLetterNew.symm.trans hLetterOld
    exact ⟨d,
      m3_initial_clone_of_canonical_parameter_lists T (F.target T)
        n d f hn hd hf (F.extendsSource T hT) hLetterEq
        hValidNew hParamList⟩
  exact F.correctedB3_of_middle_clone_varying_cut
    family n hn hLower hUpper

end SuccessorTree.V10
