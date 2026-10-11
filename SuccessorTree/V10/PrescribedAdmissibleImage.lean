import SuccessorTree.V10.PrescribedCorrectedB3
import SuccessorTree.V10.PrescribedRecordIndependence
import SuccessorTree.V10.LocalAgeNeutralImageUnique
import Mathlib.Tactic

/-!
# Actual admissible images of the prescribed matching insertion

Retain the literal finite constructor under corrected B3, rather than
forgetting it behind an arbitrary existential insertion. This lets us
construct images in the genuine forbidden-free Kpt node set and prove
that the image relation is functional using full-record independence.

No prefix or successor property is assumed in the image relation. Those
remain separate obligations before the prescribed operation is a ShapeMap.
-/

namespace SuccessorTree.V10

/-- Corrected B3 gives a forbidden-free literal prescribed constructor,
including its actual cut, old L embedding and transported free levels. -/
theorem PrescribedBoringData.matching_constructor_of_correctedB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat) (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hTargetAd : IsAdmissibleRawType family
      (⟨ell+1,F.target S0⟩ : RawPartialTypeNode db du dd)) :
    ∃ (d : Nat) (hd : d ≤ ell) (hGate : d = 0 ∨ d < ell)
      (hValid : ValidNewOrdinaryColumn (F.target S0) d),
      let B := prescribedInsertPartial A (F.target S0) d hValid
        hell hPos hd hGate (F.upperIncoming A) (F.upperOutgoing A)
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      IsLInsertion A B ell ∧
      (∀ u, u < A.size →
        B.freeLevel (insertAddress ell u) =
          if A.freeLevel u < ell then A.freeLevel u
          else A.freeLevel u + 1) := by
  apply F.matching_prescribed_constructor_exists family A base S0
    hS0 hComp hell hPos hAvoidA hTargetAd
  intro W w hQ _
  have hE : W.E ell w = true := by
    have he := admissible_level_succ_has_last_E
      family ell (F.target S0) hTargetAd
    rw [hQ] at he
    exact he
  exact F.correctedB3_to_witness_test family hB3 S0 hS0
    W w (W.E_inside ell w hE).1 hQ

/-- Extract the complete record at its stated level from an equality of
raw Sigma nodes. This small adapter avoids repeated dependent casts. -/
theorem record_eq_of_rawTypeAtFree
    {n db du dd : Nat}
    (T : PartialTypeWithE n db du dd)
    (A : EnumeratedPartialStructure db du dd) (v : Nat)
    (hRaw : (⟨n,T⟩ : RawPartialTypeNode db du dd) = A.rawTypeAtFree v) :
    T = A.partialTypeAt n v := by
  have hCut : n = A.freeLevel v := congrArg Sigma.fst hRaw
  have hPair : (⟨n,T⟩ : RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩ :
        RawPartialTypeNode db du dd) := hRaw
  have hHEq := (Sigma.mk.inj_iff.mp hPair).2
  rw [←hCut] at hHEq
  exact eq_of_heq hHEq

/-- A matching image is represented by the actual prescribed constructor.
Neither equality of images nor any successor property is an input. -/
def PrescribedBoringData.IsMatchingKptImage
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd)) (hPos : 0 < ell)
    (a b : AdmissibleKptNode family) : Prop :=
  ∃ (A : EnumeratedPartialStructure db du dd) (v : Nat)
    (S0 : PartialTypeWithE ell db du dd) (d : Nat)
    (hell : ell ≤ A.size)
    (hValid : ValidNewOrdinaryColumn (F.target S0) d)
    (hd : d ≤ ell) (hGate : d = 0 ∨ d < ell),
    v < A.size ∧
    (∀ bad, bad ∈ family → bad.Avoids A.L) ∧
    a.1 = A.rawTypeAtFree v ∧
    S0 ∈ F.source ∧
    SameOrdinaryAtCut S0 (A.partialTypeAt ell v) ∧
    b.1 = (prescribedInsertPartial A (F.target S0) d hValid
      hell hPos hd hGate (F.upperIncoming A) (F.upperOutgoing A)).rawTypeAtFree
        (insertAddress ell v)

/-- Every admissible upper node with a matching source has an admissible
literal prescribed image at exactly the next level. Admissibility of
targets is used only on the prescribed source set. -/
theorem PrescribedBoringData.matchingKptImage_exists
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)) :
    ∃ b : AdmissibleKptNode family,
      F.IsMatchingKptImage family hPos a b ∧ b.1.1 = a.1.1 + 1 := by
  obtain ⟨S0,hS0,hComp⟩ := hMatch
  obtain ⟨A,v,hv,hAvoidA,hRawA⟩ := a.2
  have hSourceLev : a.1.1 = A.freeLevel v := congrArg Sigma.fst hRawA
  have hOldCut : ell ≤ A.freeLevel v := by omega
  have hBound := A.freeLevel_le v
  have hell : ell ≤ A.size := by omega
  have hRecord : a.1.2 = A.partialTypeAt a.1.1 v :=
    record_eq_of_rawTypeAtFree a.1.2 A v hRawA
  have hSource : a.1.2.restrict hlev = A.partialTypeAt ell v := by
    rw [hRecord, A.partialTypeAt_restrict ell a.1.1 v hlev]
  have hCompA : SameOrdinaryAtCut S0 (A.partialTypeAt ell v) := by
    rw [hSource] at hComp
    exact hComp
  obtain ⟨d,hd,hGate,hValid,hAvoidB,hInsertion,hFree⟩ :=
    F.matching_constructor_of_correctedB3 family hB3 A v S0 hS0
      hCompA hell hPos hAvoidA (hTargets S0 hS0)
  let B := prescribedInsertPartial A (F.target S0) d hValid
    hell hPos hd hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hvB : insertAddress ell v < B.size := by
    change insertAddress ell v < A.size + 1
    rw [insertAddress_above ell v (hOldCut.trans hBound)]
    omega
  let b : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell v),
      ⟨B,insertAddress ell v,hvB,hAvoidB,rfl⟩⟩
  refine ⟨b,?_,?_⟩
  · exact ⟨A,v,S0,d,hell,hValid,hd,hGate,hv,hAvoidA,hRawA,
      hS0,hCompA,rfl⟩
  · change B.freeLevel (insertAddress ell v) = a.1.1 + 1
    have h := hFree v hv
    rw [if_neg (Nat.not_lt.mpr hOldCut)] at h
    exact h.trans (congrArg (fun n : Nat => n+1) hSourceLev.symm)

/-- Full-record independence makes the matching-image relation functional,
allowing different finite realizations AND different compatible sources. -/
theorem PrescribedBoringData.matchingKptImage_graph_unique
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd)) (hPos : 0 < ell)
    (a : AdmissibleKptNode family) (hlev : ell ≤ a.1.1)
    (b c : AdmissibleKptNode family)
    (hb : F.IsMatchingKptImage family hPos a b)
    (hc : F.IsMatchingKptImage family hPos a c) : b = c := by
  obtain ⟨A,v,S0,d,hellA,hValidA,hd,hGateA,hv,hAvoidA,hRawA,
    hS0,hCompA,hImgA⟩ := hb
  obtain ⟨C,w,S1,e,hellC,hValidC,he,hGateC,hw,hAvoidC,hRawC,
    hS1,hCompC,hImgC⟩ := hc
  obtain ⟨hCutEq,hTypeEq⟩ := rawTypeAtFree_eq_data A C v w
    (hRawA.symm.trans hRawC)
  let cut := A.freeLevel v
  have hOrigLev : a.1.1 = A.freeLevel v := congrArg Sigma.fst hRawA
  have hEllCut : ell ≤ cut := by omega
  have hV : cut ≤ v := A.freeLevel_le v
  have hW : cut ≤ w := by
    have h := C.freeLevel_le w
    omega
  have hCutA : cut ≤ A.size := by omega
  have hCutC : cut ≤ C.size := by omega
  have hShort : A.partialTypeAt ell v = C.partialTypeAt ell w :=
    partialTypeAt_coordinate_eq_of_fullType_eq A C ell cut v w
      hEllCut hTypeEq none
  have hCompC' : SameOrdinaryAtCut S1 (A.partialTypeAt ell v) := by
    rw [hShort]
    exact hCompC
  have hSocle := F.outputs_compatible S0 S1 (A.partialTypeAt ell v)
    hS0 hS1 hCompA hCompC'
  let B := prescribedInsertPartial A (F.target S0) d hValidA
    hellA hPos hd hGateA (F.upperIncoming A) (F.upperOutgoing A)
  let D := prescribedInsertPartial C (F.target S1) e hValidC
    hellC hPos he hGateC (F.upperIncoming C) (F.upperOutgoing C)
  have hFreeA : B.freeLevel (insertAddress ell v) = cut+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
      d hValidA hellA hPos hd hGateA
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    rw [if_neg (Nat.not_lt.mpr hEllCut)] at h
    exact h
  have hFreeC : D.freeLevel (insertAddress ell w) = cut+1 := by
    have h := prescribedInsertPartial_old_freeLevel C (F.target S1)
      e hValidC hellC hPos he hGateC
      (F.upperIncoming C) (F.upperOutgoing C) w hw
    have hn : ¬ C.freeLevel w < ell := by omega
    rw [if_neg hn, ←hCutEq] at h
    exact h
  have hT : B.partialTypeAt (cut+1) (insertAddress ell v) =
      D.partialTypeAt (cut+1) (insertAddress ell w) :=
    F.prescribedInsertPartial_independent A C (F.target S0) (F.target S1)
      d e hValidA hValidC hSocle hd he hGateA hGateC cut v w
      hPos hEllCut hCutA hCutC hV hW hv hw hTypeEq
  have hRaw : B.rawTypeAtFree (insertAddress ell v) =
      D.rawTypeAtFree (insertAddress ell w) := by
    change (⟨B.freeLevel (insertAddress ell v),
      B.partialTypeAt (B.freeLevel (insertAddress ell v))
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) =
      (⟨D.freeLevel (insertAddress ell w),
      D.partialTypeAt (D.freeLevel (insertAddress ell w))
        (insertAddress ell w)⟩ : RawPartialTypeNode db du dd)
    rw [hFreeA,hFreeC]
    exact congrArg (Sigma.mk (cut+1)) hT
  exact Subtype.ext (hImgA.trans (hRaw.trans hImgC.symm))

end SuccessorTree.V10
