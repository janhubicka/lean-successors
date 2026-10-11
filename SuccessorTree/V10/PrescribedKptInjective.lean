import SuccessorTree.V10.InsertedTypeRecovery
import SuccessorTree.V10.PrescribedKptSkip
import Mathlib.Tactic

/-!
# A common left inverse and injectivity of the prescribed Kpt map

The literal recovery operation deletes the inserted coordinate from
both kinds of upper images, and fixes lower nodes. Its left-inverse
identity proves injectivity without separating prescribed/prescribed,
neutral/neutral and mixed pairs, or assuming prefix preservation.
-/

namespace SuccessorTree.V10

/-- Raw-node recovery for the genuine prescribed finite construction. -/
theorem PrescribedBoringData.prescribedInsertPartial_raw_recovery
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hd : d ≤ ell) (hGate : d = 0 ∨ d < ell)
    (v : Nat) (hv : v < A.size) (hFree : ell ≤ A.freeLevel v) :
    recoverInsertedRaw ell
      ((prescribedInsertPartial A Q d hValid hell hPos hd hGate
        (F.upperIncoming A) (F.upperOutgoing A)).rawTypeAtFree
          (insertAddress ell v)) = A.rawTypeAtFree v := by
  let B := prescribedInsertPartial A Q d hValid hell hPos hd hGate
    (F.upperIncoming A) (F.upperOutgoing A)
  have hCut : A.freeLevel v ≤ A.size := (A.freeLevel_le v).trans (Nat.le_of_lt hv)
  have hNew : B.freeLevel (insertAddress ell v) = A.freeLevel v+1 := by
    have h := prescribedInsertPartial_old_freeLevel A Q d hValid hell hPos
      hd hGate (F.upperIncoming A) (F.upperOutgoing A) v hv
    simpa only [B, if_neg (Nat.not_lt.mpr hFree)] using h
  change recoverInsertedRaw ell
    (⟨B.freeLevel (insertAddress ell v),
      B.partialTypeAt (B.freeLevel (insertAddress ell v))
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) =
    ⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩
  rw [hNew, recoverInsertedRaw_succ ell _ hFree]
  exact congrArg (Sigma.mk (A.freeLevel v))
    (F.prescribedInsertPartial_erase A Q d hValid hell hPos hd hGate
      (A.freeLevel v) v hCut hv)

/-- Raw-node recovery for the neutral finite construction, with the
identical recovery function used for prescribed images. -/
theorem neutralInsert_raw_recovery
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hPos : 0 < ell)
    (v : Nat) (hv : v < A.size) (hFree : ell ≤ A.freeLevel v) :
    recoverInsertedRaw ell
      ((neutralInsert A ell hell hPos).rawTypeAtFree (insertAddress ell v)) =
      A.rawTypeAtFree v := by
  let B := neutralInsert A ell hell hPos
  have hCut : A.freeLevel v ≤ A.size := (A.freeLevel_le v).trans (Nat.le_of_lt hv)
  have hNew : B.freeLevel (insertAddress ell v) = A.freeLevel v+1 := by
    have h := neutralInsert_freeLevel_old A ell hell hPos v hv
    simpa only [B, if_neg (Nat.not_lt.mpr hFree)] using h
  change recoverInsertedRaw ell
    (⟨B.freeLevel (insertAddress ell v),
      B.partialTypeAt (B.freeLevel (insertAddress ell v))
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) =
    ⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩
  rw [hNew, recoverInsertedRaw_succ ell _ hFree]
  exact congrArg (Sigma.mk (A.freeLevel v))
    (neutralInsert_partialType_erase A ell hell hPos (A.freeLevel v) v hCut hv)

/-- Every literal matching image recovers its source. This result needs
neither corrected B3 nor a choice of the matching-image selector. -/
theorem PrescribedBoringData.IsMatchingKptImage.recover
    {ell db du dd : Nat} {F : PrescribedBoringData ell db du dd}
    {family : List (NormalizedForbidden db du dd)} {hPos : 0 < ell}
    {a b : AdmissibleKptNode family}
    (hImage : F.IsMatchingKptImage family hPos a b)
    (hlev : ell ≤ a.1.1) : recoverInsertedRaw ell b.1 = a.1 := by
  obtain ⟨A,v,S0,d,hell,hValid,hd,hGate,hv,hAvoidA,hRawA,
    hS0,hComp,hImg⟩ := hImage
  have hFree : ell ≤ A.freeLevel v := by
    have h : a.1.1 = A.freeLevel v := congrArg Sigma.fst hRawA
    omega
  rw [hImg]
  exact (F.prescribedInsertPartial_raw_recovery A (F.target S0) d hValid
    hell hPos hd hGate v hv hFree).trans hRawA.symm

/-- The actual total prescribed-or-neutral map has a common raw left
inverse. The proof does not compare or identify its two branches. -/
theorem PrescribedBoringData.prescribedKptSkip_recover
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) (a : AdmissibleKptNode family) :
    recoverInsertedRaw ell
      (F.prescribedKptSkip family hB3 hTargets hPos a).1 = a.1 := by
  classical
  by_cases hlev : ell ≤ a.1.1
  · by_cases hMatch : F.HasCompatibleSource (a.1.2.restrict hlev)
    · rw [F.prescribedKptSkip_matching family hB3 hTargets hPos a hlev hMatch]
      exact (F.matchingKptImage_isImage family hB3 hTargets hPos a hlev hMatch).recover hlev
    · rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos a hlev hMatch]
      obtain ⟨A,v,hell,hv,hAvoidA,hRawA,hImg⟩ :=
        neutralKptImage_isImage family ell hPos a hlev
      have hFree : ell ≤ A.freeLevel v := by
        have h : a.1.1 = A.freeLevel v := congrArg Sigma.fst hRawA
        omega
      rw [hImg]
      exact (neutralInsert_raw_recovery A ell hell hPos v hv hFree).trans hRawA.symm
  · have hLow : a.1.1 < ell := Nat.lt_of_not_ge hlev
    rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos a hLow]
    exact recoverInsertedRaw_fixed_below ell a.1 hLow

/-- Injectivity on actual admissible nodes, including mixed prescribed
and neutral images and all comparisons crossing the omitted level. -/
theorem PrescribedBoringData.prescribedKptSkip_injective
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell) :
    Function.Injective (F.prescribedKptSkip family hB3 hTargets hPos) := by
  intro a b hImage
  have h := congrArg
    (fun c : AdmissibleKptNode family => recoverInsertedRaw ell c.1) hImage
  rw [F.prescribedKptSkip_recover family hB3 hTargets hPos a,
    F.prescribedKptSkip_recover family hB3 hTargets hPos b] at h
  exact Subtype.ext h

end SuccessorTree.V10
