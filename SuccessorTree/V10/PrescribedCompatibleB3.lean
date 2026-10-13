import SuccessorTree.V10.PrescribedCorrectedB3
import SuccessorTree.V10.PrescribedBoringCompletion
import Mathlib.Tactic

/-!
# The finite age test within one ordinary L+ compatibility class

The actual insertion reads every upper source type from ONE ambient
partial structure. Those source types have a common ordinary L+ socle,
not just the same L-reduct. Retain that information when applying the
finite L-age test. The age witness itself still carries no auxiliary E.

The original CorrectedB3 API is unchanged. The weaker hypothesis below
is sufficient for the actual finite matching insertion. It is also
exactly CorrectedB3 applied separately to each compatibility class.
The derivation of this hypothesis from an arbitrary ShapeMap, and the
assembly of the classwise maps, remain separate M2 obligations.
-/

namespace SuccessorTree.V10

/-- The permitted upper L-types, retaining the source compatibility class. -/
def PrescribedBoringData.CompatibleUpperLType
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (S0 : PartialTypeWithE ell db du dd)
    (R : RelationalPrefixType (ell + 1) db du dd) : Prop :=
  ∃ T : PartialTypeWithE ell db du dd,
    T ∈ F.source ∧ SameOrdinaryAtCut T S0 ∧
      R = (F.target T).lReduct

/-- Test finite L-age separately within each full ordinary L+ socle.
No E-expansion of the numerical layout of an arbitrary witness is required. -/
def PrescribedBoringData.CompatibleB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd)) : Prop :=
  ∀ S0, S0 ∈ F.source →
    CommonSocleAgeTest family
      (prescribedOrdinarySocle (F.target S0)) ell
      (F.CompatibleUpperLType S0)

/-- The unlabelled age test implies the compatibility-restricted test. -/
theorem PrescribedBoringData.correctedB3_implies_compatibleB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CorrectedB3 family) :
    F.CompatibleB3 family := by
  intro S0 hS0 W hFinite hSame hUpper hDelete
  have hUpper' : UpperTypesPrescribed W ell F.PrescribedUpperLType := by
    intro x hx hxell
    obtain ⟨T, hT, _hComp, hType⟩ := hUpper x hx hxell
    exact ⟨T, hT, hType⟩
  exact hB3 S0 hS0 W hFinite hSame hUpper' hDelete

/-- Restrict the source without changing any prescribed value. -/
def PrescribedBoringData.restrictToCompatible
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (S0 : PartialTypeWithE ell db du dd) :
    PrescribedBoringData ell db du dd where
  source := {T | T ∈ F.source ∧ SameOrdinaryAtCut T S0}
  target := F.target
  extendsSource := fun T hT => F.extendsSource T hT.1
  preservesCompatibility := fun T U hT hU hTU =>
    F.preservesCompatibility T U hT.1 hU.1 hTU

/-- The restricted test is exactly the old test on each compatibility class. -/
theorem PrescribedBoringData.compatibleB3_iff_restricted_correctedB3
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd)) :
    F.CompatibleB3 family ↔
      ∀ S0, S0 ∈ F.source →
        (F.restrictToCompatible S0).CorrectedB3 family := by
  constructor
  · intro hB3 S0 _hS0 U hU W hFinite hSame hUpper hDelete
    have hUpper' : UpperTypesPrescribed W ell
        (F.CompatibleUpperLType U) := by
      intro x hx hxell
      obtain ⟨T, hT, hType⟩ := hUpper x hx hxell
      exact ⟨T, hT.1,
        sameOrdinaryAtCut_trans hT.2 (sameOrdinaryAtCut_symm hU.2),
        hType⟩
    exact hB3 U hU.1 W hFinite hSame hUpper' hDelete
  · intro hB3 S0 hS0 W hFinite hSame hUpper hDelete
    have hUpper' : UpperTypesPrescribed W ell
        (F.restrictToCompatible S0).PrescribedUpperLType := by
      intro x hx hxell
      obtain ⟨T, hT, hComp, hType⟩ := hUpper x hx hxell
      exact ⟨T, ⟨hT, hComp⟩, hType⟩
    exact hB3 S0 hS0 S0
      ⟨hS0, sameOrdinaryAtCut_refl S0⟩ W hFinite hSame hUpper' hDelete

/-- A linked upper vertex of the actual insertion comes from its actual
old type, in the same full ordinary L+ socle as the chosen lower column.
The non-edge rule supplies source membership rather than assuming it. -/
theorem PrescribedBoringData.insertL_linked_upper_is_compatible
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base)) :
    ∀ x : Nat, x < A.size + 1 → ell < x →
      (∃ t : Fin db,
        (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))).binary ell x t = true ∨
        (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))).binary x ell t = true) →
      F.CompatibleUpperLType S0
        (RelationalPrefixType.ofAgeModel
          (insertL A ell (F.insertedLData A
            (lowerInsertedColumn (F.target S0)))) (ell + 1) x) := by
  classical
  intro x hx hxell hLink
  let P := lowerInsertedColumn (F.target S0)
  let u := removeInserted ell x
  have hxne : x ≠ ell := by omega
  have hUx : insertAddress ell u = x :=
    insertAddress_removeInserted ell x hxne
  have hUge : ell ≤ u := by
    unfold u removeInserted
    have hn : ¬ x < ell := by omega
    simp [hn]
    omega
  have hUsize : u < A.size := by
    unfold u removeInserted
    have hn : ¬ x < ell := by omega
    simp [hn]
    omega
  have hForward (t : Fin db) :
      (insertL A ell (F.insertedLData A P)).binary ell x t =
        (F.insertedLData A P).outgoing u t := by
    simp [insertL, hxne, u]
  have hBackward (t : Fin db) :
      (insertL A ell (F.insertedLData A P)).binary x ell t =
        (F.insertedLData A P).incoming u t := by
    simp [insertL, hxne, u]
  have hDataLink : ∃ t : Fin db,
      (F.insertedLData A P).outgoing u t = true ∨
      (F.insertedLData A P).incoming u t = true := by
    obtain ⟨t, ht⟩ := hLink
    refine ⟨t, ?_⟩
    rcases ht with ht | ht
    · exact Or.inl ((hForward t).symm.trans ht)
    · exact Or.inr ((hBackward t).symm.trans ht)
  have hMem := F.linked_upper_in_source A P u hUge hDataLink
  have hGate : ell ≤ A.freeLevel u :=
    gatedInsertedLData_above A P
      (F.upperIncoming A) (F.upperOutgoing A)
      u hUge hUsize hDataLink
  have hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) = some P :=
    F.selectedLowerColumn_eq (A.partialTypeAt ell base) S0 hS0 hComp
  refine ⟨A.partialTypeAt ell u, hMem, ?_, ?_⟩
  · exact sameOrdinaryAtCut_trans
      (sameOrdinaryAtCut_sameAmbient A ell u base)
      (sameOrdinaryAtCut_symm hComp)
  · rw [← hUx]
    exact F.upper_realizes_target_L A base u P
      hUge hGate hSelected hMem

/-- Pass to a genuine target witness while retaining the compatibility class. -/
theorem PrescribedBoringData.compatibleB3_to_witness_test
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CompatibleB3 family)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (W : EnumeratedPartialStructure db du dd)
    (w : Nat) (hSize : ell < W.size)
    (hQ : F.target S0 = W.partialTypeAt (ell + 1) w) :
    CommonSocleAgeTest family W.L ell
      (F.CompatibleUpperLType S0) := by
  have hSocle := prescribedOrdinarySocle_matches_witness
    W w (F.target S0) hSize hQ
  intro V hFinite hSame hUpper hDelete
  exact hB3 S0 hS0 V hFinite (hSame.trans hSocle) hUpper hDelete

/-- The existing finite constructor is forbidden-free under the weaker
compatible-class test. Its E axioms and link gates are unchanged. -/
theorem PrescribedBoringData.prescribedInsertion_avoids_of_compatible_witness
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : PrescribedBoringData ell db du dd)
    (A W : EnumeratedPartialStructure db du dd)
    (base w : Nat)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source)
    (hComp : SameOrdinaryAtCut S0 (A.partialTypeAt ell base))
    (hell : ell ≤ A.size) (hellPos : 0 < ell)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hAvoidW : ∀ bad, bad ∈ family → bad.Avoids W.L)
    (hWSize : ell < W.size)
    (hWitness : F.target S0 = W.partialTypeAt (ell + 1) w)
    (d : Nat)
    (hValid : ValidNewOrdinaryColumn (F.target S0) d)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (hAgeTest : CommonSocleAgeTest family W.L ell
      (F.CompatibleUpperLType S0)) :
    ∀ bad, bad ∈ family →
      bad.Avoids
        (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).L := by
  have hSocle : SameInitialL
      (prescribedInsertPartial A (F.target S0) d hValid
        hell hellPos hd hdGate (F.upperIncoming A)
        (F.upperOutgoing A)).L W.L ell := by
    change SameInitialL
      (insertL A ell (F.insertedLData A
        (lowerInsertedColumn (F.target S0)))) W.L ell
    exact F.insertedData_common_initial_L A W S0 hS0 base w
      hComp hell hWSize hWitness
  have hUpper : ∀ x,
      x < (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).size →
      ell < x →
      (∃ t : Fin db,
        (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).L.binary ell x t = true ∨
        (prescribedInsertPartial A (F.target S0) d hValid
          hell hellPos hd hdGate (F.upperIncoming A)
          (F.upperOutgoing A)).L.binary x ell t = true) →
      F.CompatibleUpperLType S0
        (RelationalPrefixType.ofAgeModel
          (prescribedInsertPartial A (F.target S0) d hValid
            hell hellPos hd hdGate (F.upperIncoming A)
            (F.upperOutgoing A)).L (ell + 1) x) := by
    intro x hx hxAbove hLink
    change x < A.size + 1 at hx
    change ∃ t : Fin db,
      (insertL A ell (F.insertedLData A
        (lowerInsertedColumn (F.target S0)))).binary ell x t = true ∨
      (insertL A ell (F.insertedLData A
        (lowerInsertedColumn (F.target S0)))).binary x ell t = true
      at hLink
    change F.CompatibleUpperLType S0
      (RelationalPrefixType.ofAgeModel
        (insertL A ell (F.insertedLData A
          (lowerInsertedColumn (F.target S0)))) (ell + 1) x)
    exact F.insertL_linked_upper_is_compatible A base S0 hS0 hComp
      x hx hxAbove hLink
  exact prescribedInsertPartial_avoids_of_ageTest
    family A (F.target S0) d hValid hell hellPos hd hdGate
    (F.upperIncoming A) (F.upperOutgoing A)
    hAvoidA W.L (F.CompatibleUpperLType S0)
    hSocle hAvoidW hUpper hAgeTest

/-- Reuse the global boring-extension theorem for one compatibility class.
Assembly across all classes and the M2 specialization are separate. -/
theorem PrescribedBoringData.compatible_class_boring_extension_exists
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hB3 : F.CompatibleB3 family)
    (hTargets : ∀ S, S ∈ F.source → IsAdmissibleRawType family
      (⟨ell + 1, F.target S⟩ : RawPartialTypeNode db du dd))
    (hPos : 0 < ell)
    (S0 : PartialTypeWithE ell db du dd)
    (hS0 : S0 ∈ F.source) :
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧ Φ.SkipsOnly ell ∧
      ∀ (S : PartialTypeWithE ell db du dd)
        (hS : S ∈ F.source)
        (hComp : SameOrdinaryAtCut S S0)
        (hAdS : IsAdmissibleRawType family
          (⟨ell, S⟩ : RawPartialTypeNode db du dd)),
        (Φ (⟨⟨ell, S⟩, hAdS⟩ : AdmissibleKptNode family)).1 =
          (⟨ell + 1, F.target S⟩ : RawPartialTypeNode db du dd) := by
  have hClassB3 : (F.restrictToCompatible S0).CorrectedB3 family :=
    (F.compatibleB3_iff_restricted_correctedB3 family).1 hB3 S0 hS0
  have hClassTargets : ∀ S,
      S ∈ (F.restrictToCompatible S0).source →
      IsAdmissibleRawType family
        (⟨ell + 1, (F.restrictToCompatible S0).target S⟩ :
          RawPartialTypeNode db du dd) := by
    intro S hS
    exact hTargets S hS.1
  obtain ⟨Φ, hM, hSkip, hAgree⟩ :=
    (F.restrictToCompatible S0).prescribedKpt_boring_extension_exists
      family hClassB3 hClassTargets hPos
  refine ⟨Φ, hM, hSkip, ?_⟩
  intro S hS hComp hAdS
  exact hAgree S ⟨hS, hComp⟩ hAdS

end SuccessorTree.V10
