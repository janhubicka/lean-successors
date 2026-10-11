import SuccessorTree.V10.PrescribedOldParameter
import SuccessorTree.V10.PrescribedKptGapSucc
import SuccessorTree.V10.LocalAgeCanonicalInputs
import SuccessorTree.V10.CanonicalStepUniqueness
import Mathlib.Tactic

/-!
# Exact upper canonical successor: matching prescribed branch

The canonical source successor b is represented by an ambient A, v.
If the ell-prefix of b has a compatible prescribed source S0, form the
actual forbidden-free prescribedInsertPartial B from this A and S0.
The arbitrary-representation lemma computes the selected image of b,
while order preservation and the common level shift give a genuine
cover in the target Kpt tree. Terminal letter and empty-or-singleton
canonical parameter list are transported by the concrete finite
theorems. Canonical step uniqueness then gives exact successor equality.

The unmatched branch is separate and will reuse neutral insertion.
Nothing in the theorem assumes successor transport in advance.
-/

namespace SuccessorTree.V10

theorem PrescribedBoringData.prescribedKptSkip_succ_matching_above
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBaseHigh : ell ≤ a.1.1)
    (hMatchB : F.HasCompatibleSource
      (b.1.2.restrict (by
        have hCover := (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
        have hh : a.1.1 ≤ b.1.1 := hCover.le.1
        omega))) :
    (admissibleKptSTree family).succ
      (F.prescribedKptSkip family hB3 hTargets hPos a)
      (p.map (F.prescribedKptSkip family hB3 hTargets hPos)) c =
      some (F.prescribedKptSkip family hB3 hTargets hPos b) := by
  let n := a.1.1
  have hSource : IsCanonicalKptStep family a p c.1 b :=
    canonicalKptSucc_spec family (by
      change canonicalKptSucc family a p c.1 = some b
      exact hSucc)
  have hOldCover : a ⋖ b :=
    (admissibleKptSTree family).covBy_of_succ_eq_some hSucc
  have hbLev : b.1.1 = n+1 := by
    have h := LevelTree.covBy_level_eq hOldCover
    change b.1.1 = a.1.1+1 at h
    exact h
  have hbHigh : ell ≤ b.1.1 := by omega
  obtain ⟨A,v,hv,hAvoid,hRaw⟩ := b.2
  have hFree : A.freeLevel v = n+1 := by
    have h := congrArg Sigma.fst hRaw
    change b.1.1 = A.freeLevel v at h
    omega
  have hn : n < A.size := by
    have h := A.freeLevel_le v
    omega
  have hnGE : ell ≤ n := hBaseHigh
  have hNShift : insertAddress ell n = n+1 :=
    insertAddress_above ell n hnGE
  have hell : ell ≤ A.size := by omega
  have hSourceRecord : b.1.2 = A.partialTypeAt b.1.1 v :=
    record_eq_of_rawTypeAtFree b.1.2 A v hRaw
  have hEllType : b.1.2.restrict hbHigh = A.partialTypeAt ell v := by
    rw [hSourceRecord]
    exact A.partialTypeAt_restrict ell b.1.1 v hbHigh
  have hMatch : F.HasCompatibleSource (b.1.2.restrict hbHigh) := by
    exact hMatchB
  obtain ⟨S0,hS0,hComp⟩ := hMatchB
  have hCompA : SameOrdinaryAtCut S0 (A.partialTypeAt ell v) := by
    rw [←hEllType]
    exact hComp
  let t : AdmissibleKptNode family :=
    ⟨⟨ell+1,F.target S0⟩,hTargets S0 hS0⟩
  obtain ⟨k,hk,hGate,hValidT⟩ :=
    admissiblePrescribedCut_exists family ell t rfl
  have hValid : ValidNewOrdinaryColumn (F.target S0) k := by
    simpa [t,admissiblePrescribedRecord] using hValidT
  let B := prescribedInsertPartial A (F.target S0) k hValid
    hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    F.matching_constructor_avoids_of_valid_cut family hB3 A v S0
      hS0 hCompA hell hPos hAvoid (hTargets S0 hS0)
      k hValid hk hGate
  have hvB : insertAddress ell v < B.size := by
    change insertAddress ell v < A.size+1
    have hVG : ell ≤ v := by
      have h := A.freeLevel_le v
      omega
    rw [insertAddress_above ell v hVG]
    omega
  have hBFree : B.freeLevel (insertAddress ell v) = n+2 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
      k hValid hell hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    have hncut : ¬ A.freeLevel v < ell := by omega
    rw [if_neg hncut,hFree] at h
    exact h
  have hImage :
      (F.prescribedKptSkip family hB3 hTargets hPos b).1 =
        B.rawTypeAtFree (insertAddress ell v) := by
    rw [F.prescribedKptSkip_matching family hB3 hTargets hPos
      b hbHigh hMatch]
    exact F.matchingKptImage_raw_eq_of_representation
      family hB3 hTargets hPos b hbHigh hMatch
      A v hv hAvoid hRaw S0 hS0 hCompA k hell hValid hk hGate
  have hMappedPrefix :
      F.prescribedKptSkip family hB3 hTargets hPos a ≤
        F.prescribedKptSkip family hB3 hTargets hPos b :=
    F.prescribedKptSkip_prefix family hB3 hTargets hPos b a hOldCover.le
  have hMappedCover :
      F.prescribedKptSkip family hB3 hTargets hPos a ⋖
        F.prescribedKptSkip family hB3 hTargets hPos b := by
    apply LevelTree.covBy_of_le_level_succ hMappedPrefix
    change
      (F.prescribedKptSkip family hB3 hTargets hPos b).1.1 =
      (F.prescribedKptSkip family hB3 hTargets hPos a).1.1 + 1
    rw [F.prescribedKptSkip_level,F.prescribedKptSkip_level]
    simp [hBaseHigh,hbHigh]
    omega
  obtain ⟨p',c',hStepB⟩ :=
    canonicalKptStep_exists_of_covBy family hMappedCover
  have hInputA :=
    canonicalKptStep_inputs_of_ambient family A v n hv hAvoid
      hFree hSource hRaw
  have hInputB :=
    canonicalKptStep_inputs_of_ambient family B (insertAddress ell v)
      (n+1) hvB hAvoidB hBFree hStepB hImage
  let parA : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n,⟨A,n,hn,hAvoid,rfl⟩⟩
  have hnB : n+1 < B.size := by
    change n+1 < A.size+1
    omega
  let parB : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (n+1),⟨B,n+1,hnB,hAvoidB,rfl⟩⟩
  have hLetterA :
      c.1 = (A.partialTypeAt (n+1) v).terminalLetter := hInputA.1
  have hLetterB :
      c' = (B.partialTypeAt (n+2) (insertAddress ell v)).terminalLetter :=
    hInputB.1
  have hLetterTransport :
      (B.partialTypeAt (n+2) (insertAddress ell v)).terminalLetter =
        (A.partialTypeAt (n+1) v).terminalLetter := by
    have hh := prescribedInsertPartial_terminalLetter_eq A (F.target S0)
      k hValid hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
      n v hn hv
    rw [hNShift] at hh
    simpa only [B,Nat.add_assoc,Nat.reduceAdd] using hh
  have hLetter : c' = c.1 :=
    hLetterB.trans (hLetterTransport.trans hLetterA.symm)
  have hParamA :
      p = (if A.freeLevel n = 0 then [] else [parA]) := hInputA.2
  have hParamB :
      p' = (if B.freeLevel (n+1) = 0 then [] else [parB]) := hInputB.2
  have hParamTransport :
      (if B.freeLevel (n+1) = 0 then [] else [parB]) =
        (if A.freeLevel n = 0 then [] else [parA]).map
          (F.prescribedKptSkip family hB3 hTargets hPos) := by
    have hh := F.prescribedInsertPartial_parameterList_map family hB3
      hTargets A v S0 hS0 hCompA hell hPos hAvoid
      k hValid hk hGate n hn
    simpa only [B,parA,parB,hNShift] using hh
  have hParam :
      p' = p.map (F.prescribedKptSkip family hB3 hTargets hPos) := by
    calc
      p' = (if B.freeLevel (n+1) = 0 then [] else [parB]) := hParamB
      _ = (if A.freeLevel n = 0 then [] else [parA]).map
          (F.prescribedKptSkip family hB3 hTargets hPos) := hParamTransport
      _ = p.map (F.prescribedKptSkip family hB3 hTargets hPos) := by
          rw [hParamA]
  have hStepImage : IsCanonicalKptStep family
      (F.prescribedKptSkip family hB3 hTargets hPos a)
      (p.map (F.prescribedKptSkip family hB3 hTargets hPos))
      c.1 (F.prescribedKptSkip family hB3 hTargets hPos b) := by
    rw [←hParam,←hLetter]
    exact hStepB
  change canonicalKptSucc family
    (F.prescribedKptSkip family hB3 hTargets hPos a)
    (p.map (F.prescribedKptSkip family hB3 hTargets hPos))
    c.1 = some (F.prescribedKptSkip family hB3 hTargets hPos b)
  exact canonicalKptSucc_eq_some_of_step family hStepImage

end SuccessorTree.V10
