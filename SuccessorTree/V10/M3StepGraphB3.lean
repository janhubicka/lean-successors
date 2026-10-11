import SuccessorTree.V10.M3StepInputB3
import SuccessorTree.V10.CanonicalStepGraph
import Mathlib.Tactic

/-!
# Bridge the actual Kpt successor graph to corrected finite M3 B3

A canonical Kpt successor edge carries the complete valid one-level
L+ record, its exact empty/singleton parameter list and terminal
Sigma letter. This module eliminates the record-only placeholder
used in the finite M3 clone reduction: if the earlier n-th crossing
and the new prescribed crossing are both actual canonical Kpt steps
with the SAME parameter list and letter, the required repeated
record inputs are derived, hence corrected B3 follows.

These steps are the precise intended meaning of the M3 prescription
f(T)=S(T,p_n(T),c_n(T)). The remaining global M3 obligation is to
construct such a total prescribed system on every level-ell source
and check B1/B2; this file does not assume or prove that existence.

No E predicate is imposed on B3's arbitrary finite L-witnesses.
-/

namespace SuccessorTree.V10

/-- Extract an exact complete one-level canonical record, parameter
list and letter from an ACTUAL admissible Kpt successor step.
The target record Q is identified from the literal target node b,
not from an independently assumed record transformation. -/
theorem canonicalKptStep_hasCanonicalRecordInputs
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b)
    (m : Nat) (Q : PartialTypeWithE (m+1) db du dd)
    (hTarget : b.1 =
      (⟨m+1,Q⟩ : RawPartialTypeNode db du dd)) :
    HasCanonicalRecordInputs Q (p.map Subtype.val) c := by
  obtain ⟨ell,f,hf,R,hSource,hRawTarget,hLetter,hValid,hParam,hGate⟩ :=
    hStep
  have hRaw : (⟨m+1,Q⟩ : RawPartialTypeNode db du dd) =
      (⟨ell+1,R⟩ : RawPartialTypeNode db du dd) :=
    hTarget.symm.trans hRawTarget
  have hIdx : m + 1 = ell + 1 := congrArg Sigma.fst hRaw
  have hm : m = ell := by omega
  subst m
  have hQ : Q = R := eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  subst Q
  exact ⟨f,hf,hValid,hParam,hLetter⟩

/-- Genuine Kpt predecessor/terminal-letter duplication is enough to
establish the corrected finite L-age B3 clause. The two actual Kpt
steps may have different base levels n and ell, but use the same
canonical p and c and have exactly the specified target type records.
There is no assumed globally fixed free cut or finite E-age witness. -/
theorem PrescribedBoringData.correctedB3_of_repeated_Kpt_steps
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (hRepeat : ∀ T, T ∈ F.source →
      ∃ (a0 b0 a1 b1 : AdmissibleKptNode family)
        (p : List (AdmissibleKptNode family))
        (c : RawKptLetter db du dd),
        IsCanonicalKptStep family a0 p c b0 ∧
        IsCanonicalKptStep family a1 p c b1 ∧
        b0.1 = (⟨n+1,T.restrict (Nat.succ_le_of_lt hn)⟩ :
          RawPartialTypeNode db du dd) ∧
        b1.1 = (⟨ell+1,F.target T⟩ :
          RawPartialTypeNode db du dd)) :
    F.CorrectedB3 family := by
  have hRecords : ∀ T, T ∈ F.source →
      ∃ (p : List (RawPartialTypeNode db du dd))
        (c : PartialTypeWithE 1 db du dd),
        HasCanonicalRecordInputs
          (T.restrict (Nat.succ_le_of_lt hn)) p c ∧
        HasCanonicalRecordInputs (F.target T) p c := by
    intro T hT
    obtain ⟨a0,b0,a1,b1,p,c,hPrev,hNext,hPrevRaw,hNextRaw⟩ :=
      hRepeat T hT
    refine ⟨p.map Subtype.val,c,?_,?_⟩
    · exact canonicalKptStep_hasCanonicalRecordInputs family
        hPrev n (T.restrict (Nat.succ_le_of_lt hn)) hPrevRaw
    · exact canonicalKptStep_hasCanonicalRecordInputs family
        hNext ell (F.target T) hNextRaw
  exact F.correctedB3_of_repeated_canonical_inputs
    family n hn hRecords

end SuccessorTree.V10
