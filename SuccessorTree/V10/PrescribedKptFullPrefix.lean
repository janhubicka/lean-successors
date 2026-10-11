import SuccessorTree.V10.PrescribedKptPrefixMatching
import SuccessorTree.V10.LocalAgeNeutralFullPrefix
import Mathlib.Tactic

/-!
# All genuine Kpt prefixes for prescribed-or-neutral insertion

The matching upper-prefix theorem uses the one-filler replica. Here
we treat crossing the gap without a replica: all old L+ atoms at a
cut <= ell are unchanged in any prescribed finite insertion. This
also gives the self-prefix of every source at level ell.

The three disjoint cases now combine into genuine monotonicity of
prescribedKptSkip on admissible Kpt nodes. This is still NOT a
ShapeMap: canonical successor parameters and terminal letters remain
to be transported, and the weak crossing successor needs its own proof.
-/

namespace SuccessorTree.V10

/-- At or below ell, the genuine finite prescribed constructor copies
the COMPLETE old L+ type verbatim, including non-relations and E bits.
No B3 or source-compatibility hypothesis is needed for this identity. -/
theorem prescribedInsertPartial_type_below_gap
    {ell db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (P : PartialTypeWithE (ell+1) db du dd)
    (k : Nat) (hValid : ValidNewOrdinaryColumn P k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (upperIn upperOut : Nat → Fin db → Bool)
    (v d : Nat) (hv : v < A.size) (hd : d ≤ ell) :
    (prescribedInsertPartial A P k hValid hell hPos hk hGate
      upperIn upperOut).partialTypeAt d (insertAddress ell v) =
        A.partialTypeAt d v := by
  let B := prescribedInsertPartial A P k hValid hell hPos hk hGate
    upperIn upperOut
  have hIns := prescribedInsertPartial_isLInsertion
    A P k hValid hell hPos hk hGate upperIn upperOut
  have hCut : d ≤ A.size := hd.trans hell
  have hCoord : ∀ a : Option (Fin d),
      prefixVertexIndex (insertAddress ell v) a =
        insertAddress ell (prefixVertexIndex v a) := by
    intro a
    cases a with
    | none => rfl
    | some a =>
        change a.val = insertAddress ell a.val
        exact (insertAddress_below ell a.val
          (lt_of_lt_of_le a.isLt hd)).symm
  have hIn : ∀ a : Option (Fin d), prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hCut a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change B.L.binary
          (prefixVertexIndex (insertAddress ell v) a)
          (prefixVertexIndex (insertAddress ell v) b) r =
        A.L.binary (prefixVertexIndex v a) (prefixVertexIndex v b) r
      rw [hCoord a,hCoord b]
      exact hIns.binary _ _ (hIn a) (hIn b) r
    · intro a r
      change B.L.unary (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.unary (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.unary _ (hIn a) r
    · intro a r
      change B.L.diagonal (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.diagonal (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.diagonal _ (hIn a) r
  · intro a b
    change B.E (prefixVertexIndex (insertAddress ell v) a)
        (prefixVertexIndex (insertAddress ell v) b) =
      A.E (prefixVertexIndex v a) (prefixVertexIndex v b)
    rw [hCoord a,hCoord b]
    exact insertE_old_pair_eq A ell k hell hPos
      _ _ (hIn a) (hIn b)

/-- Any literal matching image retains all source predecessors whose
level is at most ell. This includes the entire original source node
when its level equals ell, and all crossing-gap comparisons. -/
theorem PrescribedBoringData.IsMatchingKptImage.lower_prefix
    {ell db du dd : Nat} {F : PrescribedBoringData ell db du dd}
    {family : List (NormalizedForbidden db du dd)}
    {hPos : 0 < ell}
    {a c : AdmissibleKptNode family}
    (hImage : F.IsMatchingKptImage family hPos a c)
    (hlevA : ell ≤ a.1.1)
    (b : AdmissibleKptNode family) (hba : b ≤ a)
    (hBelow : b.1.1 ≤ ell) : b ≤ c := by
  obtain ⟨A,v,S0,k,hell,hValid,hk,hGate,hv,hAvoidA,hRawA,
    hS0,hComp,hImg⟩ := hImage
  have hRawBA : b.1 ≤ a.1 := hba
  let d : Nat := b.1.1
  have hda : d ≤ a.1.1 := hRawBA.1
  have hSourceLev : a.1.1 = A.freeLevel v := congrArg Sigma.fst hRawA
  have hOldCut : ell ≤ A.freeLevel v := by omega
  have hRecordA : a.1.2 = A.partialTypeAt a.1.1 v :=
    record_eq_of_rawTypeAtFree a.1.2 A v hRawA
  have hBType : b.1.2 = A.partialTypeAt d v := by
    calc
      b.1.2 = a.1.2.restrict hda := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hda := by rw [hRecordA]
      _ = A.partialTypeAt d v :=
        A.partialTypeAt_restrict d a.1.1 v hda
  have hBNode : b.1 =
      (⟨d,A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨d,b.1.2⟩ : RawPartialTypeNode db du dd) :=
        (Sigma.eta b.1).symm
      _ = (⟨d,A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) :=
        congrArg (Sigma.mk d) hBType
  let B := prescribedInsertPartial A (F.target S0) k hValid
    hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hFree : B.freeLevel (insertAddress ell v) =
      A.freeLevel v+1 := by
    have h := prescribedInsertPartial_old_freeLevel A (F.target S0)
      k hValid hell hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v hv
    simpa only [B,if_neg (Nat.not_lt.mpr hOldCut)] using h
  have hType : B.partialTypeAt d (insertAddress ell v) =
      A.partialTypeAt d v :=
    prescribedInsertPartial_type_below_gap A (F.target S0)
      k hValid hell hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A) v d hv hBelow
  have hBImage : b.1 =
      (⟨d,B.partialTypeAt d (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨d,A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) :=
        hBNode
      _ = (⟨d,B.partialTypeAt d (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) :=
        congrArg (Sigma.mk d) hType.symm
  have hInside : d ≤ B.freeLevel (insertAddress ell v) := by
    rw [hFree]
    omega
  have hPrefix : b.1 ≤ B.rawTypeAtFree (insertAddress ell v) := by
    rw [hBImage]
    exact rawPartialType_prefix_of_cut B (insertAddress ell v) d hInside
  change b.1 ≤ c.1
  rw [hImg]
  exact hPrefix

/-- The matching image of any node precisely AT the gap extends the
source itself as a genuine complete L+ predecessor (B1 at all atoms). -/
theorem PrescribedBoringData.matchingKptImage_self_prefix_at_gap
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a : AdmissibleKptNode family)
    (hLevel : a.1.1 = ell)
    (hMatch : F.HasCompatibleSource
      (a.1.2.restrict (show ell ≤ a.1.1 by omega))) :
    a ≤ F.matchingKptImage family hB3 hTargets hPos a
      (show ell ≤ a.1.1 by omega) hMatch := by
  exact (F.matchingKptImage_isImage family hB3 hTargets hPos
    a (show ell ≤ a.1.1 by omega) hMatch).lower_prefix
      (show ell ≤ a.1.1 by omega) a le_rfl (by omega)

/-- Across the gap, the lower node is fixed and lies below the
prescribed or neutral image of its upper extension. -/
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
  rw [F.prescribedKptSkip_fixed_below family hB3 hTargets hPos b hbLow]
  by_cases hMatch : F.HasCompatibleSource (a.1.2.restrict haHigh)
  · rw [F.prescribedKptSkip_matching family hB3 hTargets hPos
      a haHigh hMatch]
    exact (F.matchingKptImage_isImage family hB3 hTargets hPos
      a haHigh hMatch).lower_prefix haHigh b hba (Nat.le_of_lt hbLow)
  · rw [F.prescribedKptSkip_neutral family hB3 hTargets hPos
      a haHigh hMatch]
    have hNeutral := neutralKptSkip_prefix_crossing
      family ell hPos a b hba hbLow haHigh
    rw [neutralKptSkip_fixed_below family ell hPos b hbLow,
      neutralKptSkip_above family ell hPos a haHigh] at hNeutral
    exact hNeutral

/-- Both matching and unmatched branches preserve every upper Kpt
predecessor, with the branch decision derived from the source prefix. -/
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
  have hraw : b.1 ≤ a.1 := hba
  have haHigh : ell ≤ a.1.1 := hbHigh.trans hraw.1
  by_cases hMatchB : F.HasCompatibleSource (b.1.2.restrict hbHigh)
  · have hMatchA : F.HasCompatibleSource (a.1.2.restrict haHigh) :=
      (F.compatibleSource_iff_of_Kpt_prefix a b hba hbHigh).1 hMatchB
    rw [F.prescribedKptSkip_matching family hB3 hTargets hPos
      b hbHigh hMatchB,
      F.prescribedKptSkip_matching family hB3 hTargets hPos
      a haHigh hMatchA]
    exact F.matchingKptImage_prefix_le family hB3 hTargets hPos
      a b hba hbHigh haHigh hMatchB hMatchA
  · exact F.prescribedKptSkip_prefix_unmatched family hB3 hTargets hPos
      a b hba hbHigh hMatchB

/-- Actual prescribed-or-neutral insertion preserves ALL complete Kpt
predecessor relations. Injectivity was independently proved by deletion.
This still does not assert exact or weak successor preservation. -/
theorem PrescribedBoringData.prescribedKptSkip_prefix
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) :
    F.prescribedKptSkip family hB3 hTargets hPos b ≤
      F.prescribedKptSkip family hB3 hTargets hPos a := by
  by_cases haLow : a.1.1 < ell
  · exact F.prescribedKptSkip_prefix_below family hB3 hTargets hPos
      a b hba haLow
  · by_cases hbHigh : ell ≤ b.1.1
    · exact F.prescribedKptSkip_prefix_above family hB3 hTargets hPos
        a b hba hbHigh
    · have hbLow : b.1.1 < ell := by omega
      have haHigh : ell ≤ a.1.1 := by omega
      exact F.prescribedKptSkip_prefix_crossing family hB3 hTargets hPos
        a b hba hbLow haHigh

end SuccessorTree.V10
