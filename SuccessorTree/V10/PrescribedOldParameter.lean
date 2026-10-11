import SuccessorTree.V10.PrescribedTerminalLetter
import SuccessorTree.V10.PrescribedImageRepresentation
import SuccessorTree.V10.PrescribedKptFullPrefix
import Mathlib.Tactic

/-!
# Canonical successor parameters in a prescribed finite insertion

A single genuine finite model A and a compatible prescribed source S0
determine an inserted model B. For every old vertex n of A, the
admissible type of the shifted old vertex in B is EXACTLY the image
under the total prescribed-or-neutral Kpt map:
* below ell, full old L+ atoms and the free cut are retained;
* at/above ell, S0 is compatible with the same ordinary socle at n,
  and the representation-independent matching image is computed in B.

This gives canonical empty-or-singleton parameter-list transport.
The global successor equation remains separate.
-/

namespace SuccessorTree.V10

/-- Changing the distinguished vertex within one ambient model does
not change the ordinary ell-socle. Thus one prescribed source
compatible at base is compatible at every other source address. -/
theorem PrescribedBoringData.compatible_same_ambient_base
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (S0 : PartialTypeWithE ell db du dd)
    (base n : Nat)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base)) :
    SameOrdinaryAtCut S0 (A.partialTypeAt ell n) := by
  exact ⟨(fun i j t => hComp.1 i j t),
    (fun i t => hComp.2.1 i t),
    (fun i t => hComp.2.2.1 i t),
    (fun i j => hComp.2.2.2 i j)⟩

/-- The total prescribed node map is represented on EVERY retained
old vertex of the SAME literal prescribed finite insertion.
There is no auxiliary hypothesis identifying the chosen global image
with this finite representative. -/
theorem PrescribedBoringData.prescribedInsertPartial_old_type_eq
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat) (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (k : Nat) (hValid : ValidNewOrdinaryColumn (F.target S0) k)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (n : Nat) (hn : n < A.size) :
    (F.prescribedKptSkip family hB3 hTargets hPos
      (⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoidA,rfl⟩⟩ :
        AdmissibleKptNode family)).1 =
      (prescribedInsertPartial A (F.target S0) k hValid
        hell hPos hk hGate (F.upperIncoming A)
        (F.upperOutgoing A)).rawTypeAtFree
        (insertAddress ell n) := by
  let a : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoidA,rfl⟩⟩
  let B := prescribedInsertPartial A (F.target S0) k hValid
    hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  by_cases hf : A.freeLevel n < ell
  · have ha : a.1.1 < ell := hf
    have hFix := F.prescribedKptSkip_fixed_below family
      hB3 hTargets hPos a ha
    have hBFree : B.freeLevel (insertAddress ell n) = A.freeLevel n := by
      have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
        k hValid hell hPos hk hGate
        (F.upperIncoming A) (F.upperOutgoing A) n hn
      simpa only [B,if_pos hf] using h
    have hBType : B.partialTypeAt (A.freeLevel n)
        (insertAddress ell n) = A.partialTypeAt (A.freeLevel n) n :=
      prescribedInsertPartial_type_below_gap A (F.target S0)
        k hValid hell hPos hk hGate
        (F.upperIncoming A) (F.upperOutgoing A)
        n (A.freeLevel n) hn (Nat.le_of_lt hf)
    calc
      (F.prescribedKptSkip family hB3 hTargets hPos a).1 = a.1 :=
        congrArg Subtype.val hFix
      _ = A.rawTypeAtFree n := rfl
      _ = B.rawTypeAtFree (insertAddress ell n) := by
        change (⟨A.freeLevel n,A.partialTypeAt (A.freeLevel n) n⟩ :
          RawPartialTypeNode db du dd) =
          (⟨B.freeLevel (insertAddress ell n),
            B.partialTypeAt (B.freeLevel (insertAddress ell n))
              (insertAddress ell n)⟩ : RawPartialTypeNode db du dd)
        rw [hBFree]
        exact congrArg (Sigma.mk (A.freeLevel n)) hBType.symm
  · have hlev : ell ≤ a.1.1 := by
      change ell ≤ A.freeLevel n
      omega
    have hSrcType : a.1.2.restrict hlev = A.partialTypeAt ell n := by
      change (A.partialTypeAt (A.freeLevel n) n).restrict hlev =
        A.partialTypeAt ell n
      exact A.partialTypeAt_restrict ell (A.freeLevel n) n hlev
    have hCompN : SameOrdinaryAtCut S0 (A.partialTypeAt ell n) :=
      F.compatible_same_ambient_base A S0 base n hComp
    have hMatch : F.HasCompatibleSource (a.1.2.restrict hlev) := by
      rw [hSrcType]
      exact ⟨S0,hS0,hCompN⟩
    rw [F.prescribedKptSkip_matching family hB3 hTargets hPos
      a hlev hMatch]
    exact F.matchingKptImage_raw_eq_of_representation family hB3
      hTargets hPos a hlev hMatch A n hn hAvoidA rfl
      S0 hS0 hCompN k hell hValid hk hGate

/-- An old vertex has free cut zero iff the corresponding retained
vertex after any prescribed insertion has free cut zero. -/
theorem prescribedInsertPartial_freeCut_zero_iff
    {ell db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (k : Nat) (hValid : ValidNewOrdinaryColumn Q k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (upperIn upperOut : Nat → Fin db → Bool)
    (n : Nat) (hn : n < A.size) :
    (prescribedInsertPartial A Q k hValid hell hPos hk hGate
      upperIn upperOut).freeLevel (insertAddress ell n) = 0 ↔
      A.freeLevel n = 0 := by
  rw [prescribedInsertPartial_old_freeLevel A Q k hValid hell
    hPos hk hGate upperIn upperOut n hn]
  by_cases h : A.freeLevel n < ell
  · simp [h]
  · simp [h]
    omega

/-- The canonical parameter list is transported by the ACTUAL total
prescribed map, for any prescribed finite model and any old vertex.
The empty case remains empty and a positive singleton is its exact
admissible image with the new E-cut. -/
theorem PrescribedBoringData.prescribedInsertPartial_parameterList_map
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat) (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (k : Nat) (hValid : ValidNewOrdinaryColumn (F.target S0) k)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (n : Nat) (hn : n < A.size) :
    let B := prescribedInsertPartial A (F.target S0) k hValid
      hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
    let src : AdmissibleKptNode family :=
      ⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoidA,rfl⟩⟩
    let hBn : insertAddress ell n < B.size := by
      change insertAddress ell n < A.size+1
      by_cases hlt : n < ell
      · rw [insertAddress_below ell n hlt]
        omega
      · rw [insertAddress_above ell n (by omega)]
        omega
    let hBAvoid : ∀ bad, bad ∈ family → bad.Avoids B.L :=
      F.matching_constructor_avoids_of_valid_cut family hB3 A base
        S0 hS0 hComp hell hPos hAvoidA (hTargets S0 hS0)
        k hValid hk hGate
    let dst : AdmissibleKptNode family :=
      ⟨B.rawTypeAtFree (insertAddress ell n),
        ⟨B,insertAddress ell n,hBn,hBAvoid,rfl⟩⟩
    (if B.freeLevel (insertAddress ell n) = 0 then [] else [dst]) =
      (if A.freeLevel n = 0 then [] else [src]).map
        (F.prescribedKptSkip family hB3 hTargets hPos) := by
  let B := prescribedInsertPartial A (F.target S0) k hValid
    hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  let src : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree n, ⟨A,n,hn,hAvoidA,rfl⟩⟩
  have hBn : insertAddress ell n < B.size := by
    change insertAddress ell n < A.size+1
    by_cases hlt : n < ell
    · rw [insertAddress_below ell n hlt]
      omega
    · rw [insertAddress_above ell n (by omega)]
      omega
  have hBAvoid : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    F.matching_constructor_avoids_of_valid_cut family hB3 A base S0
      hS0 hComp hell hPos hAvoidA (hTargets S0 hS0)
      k hValid hk hGate
  let dst : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell n),
      ⟨B,insertAddress ell n,hBn,hBAvoid,rfl⟩⟩
  change (if B.freeLevel (insertAddress ell n) = 0 then
    ([] : List (AdmissibleKptNode family)) else [dst]) =
    (if A.freeLevel n = 0 then [] else [src]).map
      (F.prescribedKptSkip family hB3 hTargets hPos)
  have hZero := prescribedInsertPartial_freeCut_zero_iff A
    (F.target S0) k hValid hell hPos hk hGate
    (F.upperIncoming A) (F.upperOutgoing A) n hn
  have hRaw :
      (F.prescribedKptSkip family hB3 hTargets hPos src).1 = dst.1 :=
    F.prescribedInsertPartial_old_type_eq family hB3 hTargets
      A base S0 hS0 hComp hell hPos hAvoidA
      k hValid hk hGate n hn
  have hNode : F.prescribedKptSkip family hB3 hTargets hPos src = dst :=
    Subtype.ext hRaw
  by_cases hz : A.freeLevel n = 0
  · have hzB : B.freeLevel (insertAddress ell n) = 0 :=
      hZero.mpr hz
    simp [hz,hzB]
  · have hzB : B.freeLevel (insertAddress ell n) ≠ 0 := by
      intro h
      exact hz (hZero.mp h)
    simp [hz,hzB,hNode]

end SuccessorTree.V10
