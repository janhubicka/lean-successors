import SuccessorTree.V10.PrescribedPrefixUpper
import SuccessorTree.V10.LocalAgeNeutralFullPrefix
import Mathlib.Tactic

/-!
# Full predecessor preservation for the concrete prescribed Kpt insertion

Three disjoint cases are necessary: both types above ell (shared matching
decision and prescribed replica), both below ell (identity), and crossing
the omitted level (complete old-record transport).

In the crossing case the prescribed image is treated as the *actual*
finite constructor, not an abstract shape map. The neutral case reuses
the independently proved neutral insertion predecessor theorem.
-/

namespace SuccessorTree.V10

/-- A lower predecessor remains below a selected prescribed matching image.
This is the omitted-level crossing, not an above-gap replica argument. -/
theorem PrescribedBoringData.matchingKptImage_prefix_crossing
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family) (hba : b ≤ a)
    (hbLow : b.1.1 < ell) (haHigh : ell ≤ a.1.1)
    (hMatchA : F.HasCompatibleSource (a.1.2.restrict haHigh)) :
    b ≤ F.matchingKptImage family hB3 hTargets hPos a haHigh hMatchA := by
  have hRawBA : b.1 ≤ a.1 := hba
  let cut : Nat := b.1.1
  have hda : cut ≤ a.1.1 := hRawBA.1
  obtain ⟨A,v,S0,k,hellA,hValid,hk,hGate,hv,hAvoidA,hRawA,
    hS0,hCompA,hImgA⟩ :=
    F.matchingKptImage_isImage family hB3 hTargets hPos
      a haHigh hMatchA
  let C := prescribedInsertPartial A (F.target S0) k hValid
    hellA hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hSourceLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRawA
  have hOldCut : ell ≤ A.freeLevel v := by omega
  have hAType : a.1.2 = A.partialTypeAt a.1.1 v :=
    record_eq_of_rawTypeAtFree a.1.2 A v hRawA
  have hBType : b.1.2 = A.partialTypeAt cut v := by
    calc
      b.1.2 = a.1.2.restrict hda := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hda := by rw [hAType]
      _ = A.partialTypeAt cut v :=
        A.partialTypeAt_restrict cut a.1.1 v hda
  have hBNode : b.1 =
      (⟨cut,A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨cut,b.1.2⟩ : RawPartialTypeNode db du dd) :=
        (Sigma.eta b.1).symm
      _ = (⟨cut,A.partialTypeAt cut v⟩ :
        RawPartialTypeNode db du dd) :=
          congrArg (Sigma.mk cut) hBType
  have hFree : C.freeLevel (insertAddress ell v) =
      A.freeLevel v+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
      k hValid hellA hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    simpa only [C,if_neg (Nat.not_lt.mpr hOldCut)] using h
  have hLowType : C.partialTypeAt cut (insertAddress ell v) =
      A.partialTypeAt cut v :=
    prescribedInsertPartial_type_below_gap A (F.target S0)
      k hValid hellA hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A)
      v cut hv (Nat.le_of_lt hbLow)
  have hBImage : b.1 =
      (⟨cut,C.partialTypeAt cut (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨cut,A.partialTypeAt cut v⟩ :
        RawPartialTypeNode db du dd) := hBNode
      _ = (⟨cut,C.partialTypeAt cut (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) :=
          congrArg (Sigma.mk cut) hLowType.symm
  have hInside : cut ≤ C.freeLevel (insertAddress ell v) := by
    rw [hFree]
    omega
  have hPrefix : b.1 ≤ C.rawTypeAtFree (insertAddress ell v) := by
    rw [hBImage]
    exact rawPartialType_prefix_of_cut C (insertAddress ell v)
      cut hInside
  change b.1 ≤
    (F.matchingKptImage family hB3 hTargets hPos a haHigh hMatchA).1
  rw [hImgA]
  exact hPrefix

/-- Two upper nodes choose the same matching/neutral branch, because
the full ell-prefix governing compatibility is identical. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix_above
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (hbHigh : ell ≤ b.1.1) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  have hRawBA : b.1 ≤ a.1 := hba
  have haHigh : ell ≤ a.1.1 := hbHigh.trans hRawBA.1
  have hMatchIff := F.compatibleSource_iff_of_prefix a b hba hbHigh
  by_cases hbMatch : F.HasCompatibleSource (b.1.2.restrict hbHigh)
  · have haMatch : F.HasCompatibleSource (a.1.2.restrict haHigh) :=
      hMatchIff.mp hbMatch
    rw [F.prescribedKptSkip_matching family hB3 hTargets hPos b
        hbHigh hbMatch,
      F.prescribedKptSkip_matching family hB3 hTargets hPos a
        haHigh haMatch]
    exact F.matchingKptImage_prefix_le family hB3 hTargets hPos
      a b hba hbHigh haHigh hbMatch haMatch
  · have haNone : ¬ F.HasCompatibleSource (a.1.2.restrict haHigh) := by
      intro h
      exact hbMatch (hMatchIff.mpr h)
    rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos b
        hbHigh hbMatch,
      F.prescribedKptSkip_neutral family hB3 hTargets hPos a
        haHigh haNone]
    exact neutralKptImage_prefix_le family ell hPos a b hba hbHigh

/-- Prefix relations crossing the omitted ell level survive irrespective
of whether the upper image is prescribed or neutral. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix_crossing
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (hbLow : b.1.1 < ell)
    (haHigh : ell ≤ a.1.1) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  by_cases hMatch : F.HasCompatibleSource (a.1.2.restrict haHigh)
  · rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos b
        hbLow,
      F.prescribedKptSkip_matching family hB3 hTargets hPos a
        haHigh hMatch]
    exact F.matchingKptImage_prefix_crossing family hB3 hTargets hPos
      a b hba hbLow haHigh hMatch
  · rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos b
        hbLow,
      F.prescribedKptSkip_neutral family hB3 hTargets hPos a
        haHigh hMatch]
    have h := neutralKptSkip_prefix_crossing family ell hPos
      a b hba hbLow haHigh
    rw [neutralKptSkip_fixed_below family ell hPos b hbLow,
      neutralKptSkip_above family ell hPos a haHigh] at h
    exact h

/-- The actual choice-based prescribed-or-neutral insertion preserves
every predecessor of every admissible node. No abstract prefix law,
same-branch hypothesis, or stronger B3 hypothesis is introduced. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family) (hba : b ≤ a) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  have hRawBA : b.1 ≤ a.1 := hba
  by_cases haLow : a.1.1 < ell
  · have hbLow : b.1.1 < ell := by
      have h := hRawBA.1
      omega
    rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a
        haLow,
      F.prescribedKptSkip_fixed_below family hB3 hTargets hPos b
        hbLow]
    exact hba
  · by_cases hbHigh : ell ≤ b.1.1
    · exact F.prescribedKptSkip_prefix_above family hB3 hTargets hPos
        a b hba hbHigh
    · have hbLow : b.1.1 < ell := by omega
      have haHigh : ell ≤ a.1.1 := by omega
      exact F.prescribedKptSkip_prefix_crossing family hB3 hTargets hPos
        a b hba hbLow haHigh

end SuccessorTree.V10
