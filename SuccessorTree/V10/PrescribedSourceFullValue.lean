import SuccessorTree.V10.PrescribedSourceE
import SuccessorTree.V10.PrescribedImageRepresentation
import Mathlib.Tactic

/-!
# Actual agreement with the prescribed partial function

The literal finite constructor now has its full L-reduct and its
independent auxiliary E comparison. Assemble these into equality of
the COMPLETE L+ target record. Then evaluate the selected matching
image through the proven arbitrary-representation adapter.

This is agreement with f on its level-ell source set, not a claim
that the total map already preserves canonical successors.
-/

namespace SuccessorTree.V10

/-- Every prescribed source is realized literally as its full L+ f
target by the finite insertion, not merely in the L-reduct. -/
theorem PrescribedBoringData.prescribedInsertPartial_source_full
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hFree : A.freeLevel v = ell)
    (hSrc : A.partialTypeAt ell v ∈ F.source)
    (hTargetAd : IsAdmissibleRawType family
      (⟨ell+1,F.target (A.partialTypeAt ell v)⟩ :
        RawPartialTypeNode db du dd))
    (k : Nat)
    (hValid : ValidNewOrdinaryColumn
      (F.target (A.partialTypeAt ell v)) k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell) :
    (prescribedInsertPartial A
      (F.target (A.partialTypeAt ell v)) k hValid
      hell hPos hk hGate (F.upperIncoming A)
      (F.upperOutgoing A)).partialTypeAt (ell+1)
      (insertAddress ell v) =
      F.target (A.partialTypeAt ell v) := by
  apply PartialTypeWithE.eq_of_atoms
  · exact F.prescribedInsertPartial_source_L A v hv hFree hSrc
      k hValid hell hPos hk hGate
  · intro x y
    exact F.prescribedInsertPartial_source_E family A v hv
      hFree hSrc hTargetAd k hValid hell hPos hk hGate x y

/-- The ACTUAL selected total prescribed insertion extends f at
every admissible domain node. The finite witness, source, chosen cut,
all L atoms and all E pairs have been eliminated from the statement. -/
theorem PrescribedBoringData.prescribedKptSkip_agrees_on_source
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (S : PartialTypeWithE ell db du dd)
    (hSrc : S ∈ F.source)
    (hAdS : IsAdmissibleRawType family
      (⟨ell,S⟩ : RawPartialTypeNode db du dd)) :
    (F.prescribedKptSkip family hB3 hTargets hPos
      (⟨⟨ell,S⟩,hAdS⟩ : AdmissibleKptNode family)).1 =
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd) := by
  let a : AdmissibleKptNode family := ⟨⟨ell,S⟩,hAdS⟩
  have hlev : ell ≤ a.1.1 := le_rfl
  have hRestr : a.1.2.restrict hlev = S := by
    change S.restrict (show ell ≤ ell from le_rfl) = S
    exact PartialTypeWithE.restrict_self S le_rfl
  have hMatch : F.HasCompatibleSource (a.1.2.restrict hlev) := by
    rw [hRestr]
    exact ⟨S,hSrc,sameOrdinaryAtCut_refl S⟩
  obtain ⟨A,v,hv,hAvoidA,hRawS⟩ := hAdS
  have hRawA : a.1 = A.rawTypeAtFree v := hRawS
  have hFree : A.freeLevel v = ell := by
    have hh := congrArg Sigma.fst hRawS
    change ell = A.freeLevel v at hh
    omega
  have hS : A.partialTypeAt ell v = S :=
    (record_eq_of_rawTypeAtFree S A v hRawS).symm
  have hASrc : A.partialTypeAt ell v ∈ F.source := by
    rw [hS]
    exact hSrc
  have hell : ell ≤ A.size := by
    have hbound := A.freeLevel_le v
    omega
  have hComp : SameOrdinaryAtCut S (A.partialTypeAt ell v) := by
    rw [hS]
    exact sameOrdinaryAtCut_refl S
  let t : AdmissibleKptNode family :=
    ⟨⟨ell+1,F.target S⟩,hTargets S hSrc⟩
  obtain ⟨k,hk,hGate,hValidT⟩ :=
    admissiblePrescribedCut_exists family ell t rfl
  have hValid : ValidNewOrdinaryColumn (F.target S) k := by
    simpa [t,admissiblePrescribedRecord] using hValidT
  let B := prescribedInsertPartial A (F.target S) k hValid
    hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hImg :
      (F.matchingKptImage family hB3 hTargets hPos a hlev hMatch).1 =
        B.rawTypeAtFree (insertAddress ell v) :=
    F.matchingKptImage_raw_eq_of_representation family hB3 hTargets
      hPos a hlev hMatch A v hv hAvoidA hRawA S hSrc hComp
      k hell hValid hk hGate
  have hAdA : IsAdmissibleRawType family
      (⟨ell+1,F.target (A.partialTypeAt ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    simpa only [hS] using hTargets S hSrc
  have hValidA : ValidNewOrdinaryColumn
      (F.target (A.partialTypeAt ell v)) k := by
    simpa only [hS] using hValid
  have hBFull : B.partialTypeAt (ell+1) (insertAddress ell v) =
      F.target S := by
    have h := F.prescribedInsertPartial_source_full family A v hv
      hFree hASrc hAdA k hValidA hell hPos hk hGate
    simpa only [hS, B] using h
  have hBFree : B.freeLevel (insertAddress ell v) = ell+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S)
      k hValid hell hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    have hn : ¬ A.freeLevel v < ell := by omega
    rw [if_neg hn,hFree] at h
    exact h
  have hBRaw : B.rawTypeAtFree (insertAddress ell v) =
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd) := by
    change (⟨B.freeLevel (insertAddress ell v),
      B.partialTypeAt (B.freeLevel (insertAddress ell v))
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) =
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd)
    rw [hBFree]
    exact congrArg (Sigma.mk (ell+1)) hBFull
  change (F.prescribedKptSkip family hB3 hTargets hPos a).1 =
    (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd)
  rw [F.prescribedKptSkip_matching family hB3 hTargets hPos
    a hlev hMatch]
  exact hImg.trans hBRaw

end SuccessorTree.V10
