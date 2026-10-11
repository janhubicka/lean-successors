import SuccessorTree.V10.PrescribedPrefixCore
import SuccessorTree.V10.PrefixReplicaAge
import Mathlib.Tactic

/-!
# Prescribed matching images preserve above-gap predecessors

This proof uses the actual finite prescribed constructor, not an
axiomatic map with a prefix law. A prefix replica of the larger type
is an admissible realization of the smaller type. Its complete ell
prefix is unchanged, so one compatible prescribed source and its
canonical inserted cut can be used in both finite structures.

Full L+ record independence then gives a literal prefix comparison
of the uniquely selected matching images. The neutral and crossing
branches are handled separately.
-/

namespace SuccessorTree.V10

theorem PrescribedBoringData.matchingKptImage_prefix_le
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family) (hba : b ≤ a)
    (hlevB : ell ≤ b.1.1) (hlevA : ell ≤ a.1.1)
    (hMatchB : F.HasCompatibleSource (b.1.2.restrict hlevB))
    (hMatchA : F.HasCompatibleSource (a.1.2.restrict hlevA)) :
    F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB ≤
      F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA := by
  have hRawBA : b.1 ≤ a.1 := hba
  let cut := b.1.1
  have hda : cut ≤ a.1.1 := hRawBA.1
  obtain ⟨A,v,hv,hAvoidA,hRawA⟩ := a.2
  have hSourceLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRawA
  have hd : cut ≤ A.freeLevel v := by omega
  have hellA : ell ≤ A.size := by
    have h := A.freeLevel_le v
    omega
  let R := prefixReplicaPartialStructure A v cut hv hd
  have hRFree : R.freeLevel (cut+1) = cut :=
    prefixReplicaPartialStructure_freeLevel A v cut hv hd
  have hvR : cut+1 < R.size := by
    change cut+1 < cut+2
    omega
  have hellR : ell ≤ R.size := by
    change ell ≤ cut+2
    omega
  have hAvoidR : ∀ bad, bad ∈ family → bad.Avoids R.L := by
    intro bad hbad
    exact bad.replica_preserves_avoidance A v cut hv hd (hAvoidA bad hbad)
  have hAType : a.1.2 = A.partialTypeAt a.1.1 v :=
    record_eq_of_rawTypeAtFree a.1.2 A v hRawA
  have hBType : b.1.2 = A.partialTypeAt cut v := by
    calc
      b.1.2 = a.1.2.restrict hda := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hda := by rw [hAType]
      _ = A.partialTypeAt cut v :=
        A.partialTypeAt_restrict cut a.1.1 v hda
  have hRawB :
      b.1 = (⟨cut,A.partialTypeAt cut v⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨cut,b.1.2⟩ : RawPartialTypeNode db du dd) :=
        (Sigma.eta b.1).symm
      _ = (⟨cut,A.partialTypeAt cut v⟩ :
        RawPartialTypeNode db du dd) :=
          congrArg (Sigma.mk cut) hBType
  have hRepRaw : R.rawTypeAtFree (cut+1) =
      (⟨cut,A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd) := by
    change
      (⟨R.freeLevel (cut+1),
        R.partialTypeAt (R.freeLevel (cut+1)) (cut+1)⟩ :
          RawPartialTypeNode db du dd) =
      (⟨cut,A.partialTypeAt cut v⟩ : RawPartialTypeNode db du dd)
    rw [hRFree]
    exact congrArg (Sigma.mk cut)
      (prefixReplicaPartialStructure_type_eq A v cut hv hd)
  have hRepB : b.1 = R.rawTypeAtFree (cut+1) :=
    hRawB.trans hRepRaw.symm
  have hShort : A.partialTypeAt ell v = R.partialTypeAt ell (cut+1) := by
    calc
      A.partialTypeAt ell v =
          (A.partialTypeAt cut v).restrict hlevB :=
        (A.partialTypeAt_restrict ell cut v hlevB).symm
      _ = (R.partialTypeAt cut (cut+1)).restrict hlevB := by
        rw [prefixReplicaPartialStructure_type_eq A v cut hv hd]
      _ = R.partialTypeAt ell (cut+1) :=
        R.partialTypeAt_restrict ell cut (cut+1) hlevB
  have hASource : a.1.2.restrict hlevA = A.partialTypeAt ell v := by
    rw [hAType, A.partialTypeAt_restrict ell a.1.1 v hlevA]
  have hMatchACopy := hMatchA
  obtain ⟨S0,hS0,hComp0⟩ := hMatchACopy
  have hCompA : SameOrdinaryAtCut S0 (A.partialTypeAt ell v) := by
    rw [← hASource]
    exact hComp0
  have hCompR : SameOrdinaryAtCut S0 (R.partialTypeAt ell (cut+1)) := by
    rw [← hShort]
    exact hCompA
  let q : AdmissibleKptNode family :=
    ⟨(⟨ell+1,F.target S0⟩ : RawPartialTypeNode db du dd),
      hTargets S0 hS0⟩
  have hq : q.1.1 = ell+1 := rfl
  obtain ⟨k,hk,hGate,hValid0⟩ :=
    admissiblePrescribedCut_exists family ell q hq
  have hValid : ValidNewOrdinaryColumn (F.target S0) k := by
    simpa [q,admissiblePrescribedRecord] using hValid0
  let C := prescribedInsertPartial A (F.target S0) k hValid hellA
    hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  let D := prescribedInsertPartial R (F.target S0) k hValid hellR
    hPos hk hGate (F.upperIncoming R) (F.upperOutgoing R)
  have hImgA :
      (F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA).1 =
        C.rawTypeAtFree (insertAddress ell v) :=
    F.matchingKptImage_raw_eq_of_representation family hB3 hTargets hPos
      a hlevA hMatchA A v hv hAvoidA hRawA S0 hS0 hCompA
      k hellA hValid hk hGate
  have hImgB :
      (F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB).1 =
        D.rawTypeAtFree (insertAddress ell (cut+1)) :=
    F.matchingKptImage_raw_eq_of_representation family hB3 hTargets hPos
      b hlevB hMatchB R (cut+1) hvR hAvoidR hRepB S0 hS0 hCompR
      k hellR hValid hk hGate
  have hCutA : ell ≤ A.freeLevel v := by omega
  have hCutR : ell ≤ R.freeLevel (cut+1) := by omega
  have hFreeA : C.freeLevel (insertAddress ell v) =
      A.freeLevel v+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
      k hValid hellA hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    simpa only [C,if_neg (Nat.not_lt.mpr hCutA)] using h
  have hFreeR : D.freeLevel (insertAddress ell (cut+1)) = cut+1 := by
    have h := prescribedInsertPartial_old_freeLevel R (F.target S0)
      k hValid hellR hPos hk hGate
      (F.upperIncoming R) (F.upperOutgoing R) (cut+1) hvR
    rw [if_neg (Nat.not_lt.mpr hCutR), hRFree] at h
    exact h
  have hType : C.partialTypeAt (cut+1) (insertAddress ell v) =
      D.partialTypeAt (cut+1) (insertAddress ell (cut+1)) :=
    F.prescribedInsert_prefixReplica_type_eq A (F.target S0)
      k hValid hk hGate v cut hv hd hPos hlevB
  have hRawD :
      D.rawTypeAtFree (insertAddress ell (cut+1)) =
      (⟨cut+1,C.partialTypeAt (cut+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    change
      (⟨D.freeLevel (insertAddress ell (cut+1)),
        D.partialTypeAt (D.freeLevel (insertAddress ell (cut+1)))
          (insertAddress ell (cut+1))⟩ : RawPartialTypeNode db du dd) =
      (⟨cut+1,C.partialTypeAt (cut+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd)
    rw [hFreeR]
    exact congrArg (Sigma.mk (cut+1)) hType.symm
  have hBound : cut+1 ≤ C.freeLevel (insertAddress ell v) := by
    rw [hFreeA]
    omega
  have hPrefix : D.rawTypeAtFree (insertAddress ell (cut+1)) ≤
      C.rawTypeAtFree (insertAddress ell v) := by
    rw [hRawD]
    exact rawPartialType_prefix_of_cut C
      (insertAddress ell v) (cut+1) hBound
  change
    (F.matchingKptImage family hB3 hTargets hPos b hlevB hMatchB).1 ≤
      (F.matchingKptImage family hB3 hTargets hPos a hlevA hMatchA).1
  rw [hImgB,hImgA]
  exact hPrefix

end SuccessorTree.V10
