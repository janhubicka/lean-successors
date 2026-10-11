import SuccessorTree.V10.PrescribedImageRepresentation
import SuccessorTree.V10.LocalAgeNeutralPrefix
import Mathlib.Tactic

/-!
# Prescribed insertion preserves prefixes above the gap

The common shorter source prefix determines the compatibility branch.
For matching images, realize the shorter node by the existing one-filler
prefix replica and compute its selected image with the same prescribed
source and insertion cut as the longer image. Complete-record independence
then identifies it with the appropriate prefix of the longer image.

No additional compatibility or age assumption is imposed on the node map.
The crossing-gap case is treated separately in PrescribedKptFullPrefix.
-/

namespace SuccessorTree.V10

/-- Comparable full records have identical restrictions at every common cut. -/
theorem rawPartialTypePrefix_restrict_eq
    {db du dd : Nat} (a b : RawPartialTypeNode db du dd)
    (hba : b ≤ a) (k : Nat) (hkb : k ≤ b.1) (hka : k ≤ a.1) :
    b.2.restrict hkb = a.2.restrict hka := by
  calc
    b.2.restrict hkb = (a.2.restrict hba.1).restrict hkb := by rw [hba.2]
    _ = a.2.restrict hka := a.2.restrict_trans hkb hba.1

/-- The two upper nodes necessarily make the same compatibility decision. -/
theorem PrescribedBoringData.hasCompatibleSource_prefix_iff
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family) (hba : b ≤ a)
    (hlevA : ell ≤ a.1.1) (hlevB : ell ≤ b.1.1) :
    F.HasCompatibleSource (b.1.2.restrict hlevB) ↔
      F.HasCompatibleSource (a.1.2.restrict hlevA) := by
  rw [rawPartialTypePrefix_restrict_eq a.1 b.1 hba ell hlevB hlevA]

/-- Selected matching images preserve the actual complete-record prefix
relation. The two matching proofs are only the selector's domain arguments;
the total-map theorem below derives their equivalence from the source order. -/
theorem PrescribedBoringData.matchingKptImage_prefix_le
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family) (hba : b ≤ a)
    (hlevA : ell ≤ a.1.1) (hlevB : ell ≤ b.1.1)
    (hMatchA : F.HasCompatibleSource (a.1.2.restrict hlevA))
    (hMatchB : F.HasCompatibleSource (b.1.2.restrict hlevB)) :
    F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB ≤
      F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA := by
  have hRawBA : b.1 ≤ a.1 := hba
  let n : Nat := b.1.1
  have hna : n ≤ a.1.1 := hRawBA.1
  obtain ⟨A,v,S0,e,hellA,hValid,he,hGate,hv,hAvoidA,hRawA,
    hS0,hCompA,hImgA⟩ :=
    F.matchingKptImage_isImage family hB3 hTargets hPos a hlevA hMatchA
  have hSourceLev : a.1.1 = A.freeLevel v := congrArg Sigma.fst hRawA
  have hn : n ≤ A.freeLevel v := by omega
  have hEllN : ell ≤ n := hlevB
  have hnv : n ≤ v := hn.trans (A.freeLevel_le v)
  have hCutA : n ≤ A.size := hnv.trans (Nat.le_of_lt hv)
  let R := prefixReplicaPartialStructure A v n hv hn
  have hRFree : R.freeLevel (n+1) = n :=
    prefixReplicaPartialStructure_freeLevel A v n hv hn
  have hvR : n+1 < R.size := by change n+1 < n+2; omega
  have hellR : ell ≤ R.size := by change ell ≤ n+2; omega
  have hCutR : n ≤ R.size := by change n ≤ n+2; omega
  have hAvoidR : ∀ bad, bad ∈ family → bad.Avoids R.L := by
    intro bad hbad
    exact bad.replica_preserves_avoidance A v n hv hn (hAvoidA bad hbad)
  have hSource : A.partialTypeAt n v = R.partialTypeAt n (n+1) :=
    (prefixReplicaPartialStructure_type_eq A v n hv hn).symm
  have hEllSource : A.partialTypeAt ell v = R.partialTypeAt ell (n+1) := by
    rw [← A.partialTypeAt_restrict ell n v hEllN, hSource,
      R.partialTypeAt_restrict ell n (n+1) hEllN]
  have hCompR : SameOrdinaryAtCut S0 (R.partialTypeAt ell (n+1)) := by
    rw [← hEllSource]
    exact hCompA
  have hRecordA : a.1.2 = A.partialTypeAt a.1.1 v :=
    record_eq_of_rawTypeAtFree a.1.2 A v hRawA
  have hRecordB : b.1.2 = A.partialTypeAt n v := by
    calc
      b.1.2 = a.1.2.restrict hna := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hna := by rw [hRecordA]
      _ = A.partialTypeAt n v := A.partialTypeAt_restrict n a.1.1 v hna
  have hRawB : b.1 = (⟨n,A.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨n,b.1.2⟩ : RawPartialTypeNode db du dd) := (Sigma.eta b.1).symm
      _ = ⟨n,A.partialTypeAt n v⟩ := congrArg (Sigma.mk n) hRecordB
  have hReplicaRaw : R.rawTypeAtFree (n+1) =
      (⟨n,A.partialTypeAt n v⟩ : RawPartialTypeNode db du dd) := by
    change (⟨R.freeLevel (n+1),R.partialTypeAt (R.freeLevel (n+1)) (n+1)⟩ :
      RawPartialTypeNode db du dd) = ⟨n,A.partialTypeAt n v⟩
    rw [hRFree]
    exact congrArg (Sigma.mk n) hSource.symm
  have hRepB : b.1 = R.rawTypeAtFree (n+1) := hRawB.trans hReplicaRaw.symm
  have hImgB := F.matchingKptImage_raw_eq_of_representation family hB3
    hTargets hPos b hlevB hMatchB R (n+1) hvR hAvoidR hRepB
    S0 hS0 hCompR e hellR hValid he hGate
  let B := prescribedInsertPartial A (F.target S0) e hValid hellA hPos he hGate
    (F.upperIncoming A) (F.upperOutgoing A)
  let Q := prescribedInsertPartial R (F.target S0) e hValid hellR hPos he hGate
    (F.upperIncoming R) (F.upperOutgoing R)
  have hFreeA : ell ≤ A.freeLevel v := by omega
  have hFreeR : ell ≤ R.freeLevel (n+1) := by rw [hRFree]; exact hEllN
  have hNewA : B.freeLevel (insertAddress ell v) = A.freeLevel v+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0) e hValid
      hellA hPos he hGate (F.upperIncoming A) (F.upperOutgoing A) v hv
    simpa only [B, if_neg (Nat.not_lt.mpr hFreeA)] using h
  have hNewR : Q.freeLevel (insertAddress ell (n+1)) = n+1 := by
    have h := prescribedInsertPartial_old_freeLevel R (F.target S0) e hValid
      hellR hPos he hGate (F.upperIncoming R) (F.upperOutgoing R) (n+1) hvR
    rw [if_neg (Nat.not_lt.mpr hFreeR), hRFree] at h
    exact h
  have hType : B.partialTypeAt (n+1) (insertAddress ell v) =
      Q.partialTypeAt (n+1) (insertAddress ell (n+1)) :=
    F.prescribedInsertPartial_independent A R (F.target S0) (F.target S0)
      e e hValid hValid (sameOrdinarySocle_refl (F.target S0))
      he he hGate hGate n v (n+1) hPos hEllN hCutA hCutR
      hnv (Nat.le_succ n) hv hvR hSource
  have hRawQ : Q.rawTypeAtFree (insertAddress ell (n+1)) =
      (⟨n+1,B.partialTypeAt (n+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    change (⟨Q.freeLevel (insertAddress ell (n+1)),
      Q.partialTypeAt (Q.freeLevel (insertAddress ell (n+1)))
        (insertAddress ell (n+1))⟩ : RawPartialTypeNode db du dd) =
      ⟨n+1,B.partialTypeAt (n+1) (insertAddress ell v)⟩
    rw [hNewR]
    exact congrArg (Sigma.mk (n+1)) hType.symm
  have hBound : n+1 ≤ B.freeLevel (insertAddress ell v) := by rw [hNewA]; omega
  have hPrefix : Q.rawTypeAtFree (insertAddress ell (n+1)) ≤
      B.rawTypeAtFree (insertAddress ell v) := by
    rw [hRawQ]
    exact rawPartialType_prefix_of_cut B (insertAddress ell v) (n+1) hBound
  change (F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB).1 ≤
    (F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA).1
  rw [hImgB,hImgA]
  exact hPrefix

/-- The concrete prescribed-or-neutral map preserves every prefix whose
shorter node is at or above ell. Mixed branches cannot occur along this chain. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix_above
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family) (hba : b ≤ a)
    (hlevB : ell ≤ b.1.1) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  classical
  have hRawBA : b.1 ≤ a.1 := hba
  have hlevA : ell ≤ a.1.1 := hlevB.trans hRawBA.1
  have hIff := F.hasCompatibleSource_prefix_iff a b hba hlevA hlevB
  by_cases hMatchB : F.HasCompatibleSource (b.1.2.restrict hlevB)
  · have hMatchA := hIff.mp hMatchB
    rw [F.prescribedKptSkip_matching family hB3 hTargets hPos b hlevB hMatchB,
      F.prescribedKptSkip_matching family hB3 hTargets hPos a hlevA hMatchA]
    exact F.matchingKptImage_prefix_le family hB3 hTargets hPos a b hba
      hlevA hlevB hMatchA hMatchB
  · have hMatchA : ¬ F.HasCompatibleSource (a.1.2.restrict hlevA) :=
      fun h => hMatchB (hIff.mpr h)
    rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos b hlevB hMatchB,
      F.prescribedKptSkip_neutral family hB3 hTargets hPos a hlevA hMatchA]
    exact neutralKptImage_prefix_le family ell hPos a b hba hlevB

end SuccessorTree.V10
