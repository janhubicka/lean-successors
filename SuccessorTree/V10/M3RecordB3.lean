import SuccessorTree.V10.M3VariableCutB3
import SuccessorTree.V10.M3CanonicalCloneInitial
import SuccessorTree.V10.M3CanonicalCloneLetter
import Mathlib.Tactic

/-!
# Corrected M3 B3 follows from the actual duplicate's canonical inputs

For each prescribed source type T at level ell, suppose its output
f(T) is a genuine one-level canonical successor of T that repeats
the earlier n-th terminal letter and canonical shortened parameter.
The new ordinary free cut d may depend on T, as it does in M3.

The previous finite record lemmas derive the exact lower clone column
and the uniform upper pair-copy identities. The finite irreducible
projection then supplies the corrected B3 condition *on arbitrary
finite L-age witnesses*. This proof has no global free-cut parameter,
no E-age requirement and no independent forbidden-age hypothesis.

The remaining interface is to derive these canonical inputs from
the actual manuscript M3 prescription f(T)=S(T,p_n(T),c_n(T));
this theorem does not postulate the global M3 conclusion.
-/

namespace SuccessorTree.V10

/-- One general form of the exact M3 one-step successor data.
The valid new cut d is chosen separately for each source.
When d=0 there is no canonical parameter, and its equality is
unnecessary; the repeated terminal Sigma letter handles the singleton. -/
theorem PrescribedBoringData.correctedB3_of_canonical_M3_records
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (hCanonical : ∀ T, T ∈ F.source →
      ∃ (d : Nat) (hd : d ≤ n),
        ValidNewOrdinaryColumn (F.target T) d ∧
        (F.target T).terminalLetter =
          earlierTerminalLetter T n hn ∧
        (0 < d →
          (F.target T).lastOrdinaryParameter d
              (hd.trans (Nat.le_of_lt hn)) =
            earlierOrdinaryParameter T n d hn hd)) :
    F.CorrectedB3 family := by
  have hLetters : ∀ T, T ∈ F.source →
      (F.target T).terminalLetter =
        earlierTerminalLetter T n hn := by
    intro T hT
    obtain ⟨d,hd,hValid,hLetter,hPar⟩ := hCanonical T hT
    exact hLetter
  have hUpper : F.MiddleCloneUpperL n hn :=
    F.middleCloneUpperL_of_terminalLetter n hn hLetters
  have hLower : ∀ T, T ∈ F.source →
      ∃ d : Nat,
        MiddleCloneInitialL
          (prescribedOrdinarySocle (F.target T)) n ell d := by
    intro T hT
    obtain ⟨d,hd,hValid,hLetter,hPar⟩ := hCanonical T hT
    exact ⟨d,
      m3_initial_clone_of_canonical_records T (F.target T)
        n d hn hd (F.extendsSource T hT)
        hLetter hPar hValid⟩
  exact F.correctedB3_of_middle_clone_varying_cut
    family n hn hLower hUpper

end SuccessorTree.V10
