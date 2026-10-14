import SuccessorTree.V10.PrescribedKptPrefixCases
import Mathlib.Tactic

/-!
# Genuine matching Kpt images preserve all upper predecessors

For b <= a of levels at least ell, the preceding module shows the
compatibility test is identical. In the matching branch, represent a
in a forbidden-free finite partial structure A. A one-filler prefix
replica R represents b and has the same full ell-source record.

Use one compatible prescribed source S0 and one canonical cut of
F.target S0 for BOTH finite inserted models. Corrected B3 supplies
their forbidden-free age; the arbitrary-representation theorem then
identifies each selected Kpt image with its literal insertion. Full
inserted-record independence at the shorter cut supplies the prefix.

No abstract predecessor property is assumed and the auxiliary E
relation is part of the equality at every step.
-/

namespace SuccessorTree.V10

/-- The selected matching images of comparable upper Kpt nodes are
prefix-comparable. The two finite representatives and their distinguished
vertices may differ; the canonical inserted cut is shared and derived
from admissibility of the target. -/
theorem PrescribedBoringData.matchingKptImage_prefix_le
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a)
    (hlevB : ell ≤ b.1.1)
    (hlevA : ell ≤ a.1.1)
    (hMatchB : F.HasCompatibleSource (b.1.2.restrict hlevB))
    (hMatchA : F.HasCompatibleSource (a.1.2.restrict hlevA)) :
    F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB ≤
      F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA := by
  have hRawBA : b.1 ≤ a.1 := hba
  let cut : Nat := b.1.1
  have hda : cut ≤ a.1.1 := hRawBA.1
  obtain ⟨A,v,hv,hAvoidA,hRawA⟩ := a.2
  have hSourceLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRawA
  have hd : cut ≤ A.freeLevel v := by omega
  have hV : cut ≤ v := hd.trans (A.freeLevel_le v)
  have hCutA : cut ≤ A.size := by omega
  have hellA : ell ≤ A.size := by omega
  have hEllD : ell ≤ cut := hlevB
  let R := prefixReplicaPartialStructure A v cut hv hd
  have hRFree : R.freeLevel (cut+1) = cut :=
    prefixReplicaPartialStructure_freeLevel A v cut hv hd
  have hvR : cut+1 < R.size := by
    change cut+1 < cut+2
    omega
  have hellR : ell ≤ R.size := by
    change ell ≤ cut+2
    omega
  have hCutR : cut ≤ R.size := by
    change cut ≤ cut+2
    omega
  have hAvoidR : ∀ bad, bad ∈ family → bad.Avoids R.L := by
    intro bad hbad
    exact bad.replica_preserves_avoidance A v cut hv hd (hAvoidA bad hbad)
  have hRecordA : a.1.2 = A.partialTypeAt a.1.1 v :=
    record_eq_of_rawTypeAtFree a.1.2 A v hRawA
  have hRawBType : b.1.2 = A.partialTypeAt cut v := by
    calc
      b.1.2 = a.1.2.restrict hda := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hda := by rw [hRecordA]
      _ = A.partialTypeAt cut v :=
        A.partialTypeAt_restrict cut a.1.1 v hda
  have hRawB : b.1 =
      (⟨cut, A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨cut,b.1.2⟩ : RawPartialTypeNode db du dd) := (Sigma.eta b.1).symm
      _ = (⟨cut,A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd) :=
        congrArg (Sigma.mk cut) hRawBType
  have hReplicaFull : R.partialTypeAt cut (cut+1) =
      A.partialTypeAt cut v :=
    prefixReplicaPartialStructure_type_eq A v cut hv hd
  have hReplicaRaw : R.rawTypeAtFree (cut+1) =
      (⟨cut,A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd) := by
    change
      (⟨R.freeLevel (cut+1),
        R.partialTypeAt (R.freeLevel (cut+1)) (cut+1)⟩ :
        RawPartialTypeNode db du dd) =
        (⟨cut,A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd)
    rw [hRFree]
    exact congrArg (Sigma.mk cut) hReplicaFull
  have hRepB : b.1 = R.rawTypeAtFree (cut+1) :=
    hRawB.trans hReplicaRaw.symm
  have hMatchACopy := hMatchA
  obtain ⟨S0,hS0,hComp⟩ := hMatchACopy
  have hSourceA : a.1.2.restrict hlevA = A.partialTypeAt ell v := by
    rw [hRecordA]
    exact A.partialTypeAt_restrict ell a.1.1 v hlevA
  have hCompA : SameOrdinaryAtCut S0 (A.partialTypeAt ell v) := by
    rw [hSourceA] at hComp
    exact hComp
  have hSourceR : R.partialTypeAt ell (cut+1) =
      A.partialTypeAt ell v := by
    calc
      R.partialTypeAt ell (cut+1) =
          (R.partialTypeAt cut (cut+1)).restrict hEllD :=
        (R.partialTypeAt_restrict ell cut (cut+1) hEllD).symm
      _ = (A.partialTypeAt cut v).restrict hEllD :=
        congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.restrict hEllD) hReplicaFull
      _ = A.partialTypeAt ell v :=
        A.partialTypeAt_restrict ell cut v hEllD
  have hCompR : SameOrdinaryAtCut S0 (R.partialTypeAt ell (cut+1)) := by
    rw [hSourceR]
    exact hCompA
  let t : AdmissibleKptNode family :=
    ⟨⟨ell+1,F.target S0⟩,hTargets S0 hS0⟩
  obtain ⟨k,hk,hGate,hValidT⟩ :=
    admissiblePrescribedCut_exists family ell t rfl
  have hValid : ValidNewOrdinaryColumn (F.target S0) k := by
    simpa only [admissiblePrescribedRecord, t] using hValidT
  have hImgA :
      (F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA).1 =
        (prescribedInsertPartial A (F.target S0) k hValid hellA
          hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)).rawTypeAtFree
            (insertAddress ell v) :=
    F.matchingKptImage_raw_eq_of_representation family hB3 hTargets hPos
      a hlevA hMatchA A v hv hAvoidA hRawA S0 hS0 hCompA
      k hellA hValid hk hGate
  have hImgB :
      (F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB).1 =
        (prescribedInsertPartial R (F.target S0) k hValid hellR
          hPos hk hGate (F.upperIncoming R) (F.upperOutgoing R)).rawTypeAtFree
            (insertAddress ell (cut+1)) :=
    F.matchingKptImage_raw_eq_of_representation family hB3 hTargets hPos
      b hlevB hMatchB R (cut+1) hvR hAvoidR hRepB S0 hS0 hCompR
      k hellR hValid hk hGate
  let B := prescribedInsertPartial A (F.target S0) k hValid
    hellA hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  let Q := prescribedInsertPartial R (F.target S0) k hValid
    hellR hPos hk hGate (F.upperIncoming R) (F.upperOutgoing R)
  have hFreeA : B.freeLevel (insertAddress ell v) =
      A.freeLevel v+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
      k hValid hellA hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    have hGE : ell ≤ A.freeLevel v := by omega
    simpa only [B,if_neg (Nat.not_lt.mpr hGE)] using h
  have hFreeR : Q.freeLevel (insertAddress ell (cut+1)) = cut+1 := by
    have h := prescribedInsertPartial_old_freeLevel R (F.target S0)
      k hValid hellR hPos hk hGate
      (F.upperIncoming R) (F.upperOutgoing R) (cut+1) hvR
    have hGE : ell ≤ R.freeLevel (cut+1) := by omega
    rw [if_neg (Nat.not_lt.mpr hGE), hRFree] at h
    exact h
  have hType : B.partialTypeAt (cut+1) (insertAddress ell v) =
      Q.partialTypeAt (cut+1) (insertAddress ell (cut+1)) :=
    F.prescribedInsertPartial_independent A R
      (F.target S0) (F.target S0) k k hValid hValid
      (sameOrdinarySocle_refl (F.target S0))
      hk hk hGate hGate cut v (cut+1) hPos hEllD
      hCutA hCutR hV (by omega) hv hvR hReplicaFull.symm
  have hRawQ : Q.rawTypeAtFree (insertAddress ell (cut+1)) =
      (⟨cut+1, B.partialTypeAt (cut+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    change
      (⟨Q.freeLevel (insertAddress ell (cut+1)),
        Q.partialTypeAt (Q.freeLevel (insertAddress ell (cut+1)))
          (insertAddress ell (cut+1))⟩ : RawPartialTypeNode db du dd) =
      (⟨cut+1,B.partialTypeAt (cut+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd)
    rw [hFreeR]
    exact congrArg (Sigma.mk (cut+1)) hType.symm
  have hBound : cut+1 ≤ B.freeLevel (insertAddress ell v) := by
    rw [hFreeA]
    omega
  have hPrefix : Q.rawTypeAtFree (insertAddress ell (cut+1)) ≤
      B.rawTypeAtFree (insertAddress ell v) := by
    rw [hRawQ]
    exact rawPartialType_prefix_of_cut B
      (insertAddress ell v) (cut+1) hBound
  change
    (F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB).1 ≤
      (F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA).1
  rw [hImgB,hImgA]
  exact hPrefix

end SuccessorTree.V10
