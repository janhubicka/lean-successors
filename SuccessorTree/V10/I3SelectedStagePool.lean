import SuccessorTree.V10.I3EligibleStageWitness
import SuccessorTree.V10.I3StageSignatureBound
import SuccessorTree.V10.I3AmbientSocleBridge
import Mathlib.Tactic

/-!
# Section 6: the selected rather than all-eligible I3 source

The actual function f_ell from Algorithm 5.4 has source given by
the selected closure, not by ALL ambient originals whose E-free cut
reaches ell+1.  Enlarging the source or choosing a different next
type can silently change the B3 test.  This module isolates exactly
the additional source/target agreement needed for the manuscript.

The finite original-name universe Fin M stays fixed over all cuts.
A varying predicate Selected records which names actually occur in
the current closure; the free-cut guard is enforced separately.
The resulting prescribed map has B1/B2, admissible targets and an
exact finite L-only failed-B3 witness retaining Selected and free-cut
information.

The final selected-stage/Algorithm-5.4 identification requires a
proof from the concrete closure invariant and the failure of I2.
It is NOT asserted as a theorem without those hypotheses.
-/

namespace SuccessorTree.V10

/-- Cut-dependent restriction to originals ACTUALLY represented in
the selected closure. This is not the potentially larger pool of all
ambient originals with a sufficiently long free cut. -/
noncomputable def selectedStagePoolPrescribedData
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop) :
    PrescribedBoringData ell db du dd :=
  eligibleAmbientPoolPrescribedData A ell
    (fun v => (original v).val)
    (fun v => Selected v ∧ ell+1 ≤ A.freeLevel (original v).val)

/-- Actual selected source and prescribed output have one SAME
selected and cut-eligible original, including full absent L atoms. -/
theorem selectedStagePoolPrescribedData_source_original
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (selectedStagePoolPrescribedData A ell original Selected).source) :
    ∃ v : Fin M, Selected v ∧
      ell+1 ≤ A.freeLevel (original v).val ∧
      T = A.partialTypeAt ell (original v).val ∧
      (selectedStagePoolPrescribedData A ell original Selected).target T =
        A.partialTypeAt (ell+1) (original v).val := by
  obtain ⟨v,hBoth,hOld,hTarget⟩ :=
    eligibleAmbientPoolPrescribedData_source_original A ell
      (fun v => (original v).val)
      (fun v => Selected v ∧ ell+1 ≤ A.freeLevel (original v).val)
      T hT
  exact ⟨v,hBoth.1,hBoth.2,hOld,hTarget⟩

/-- Every selected output is a genuine admissible Kpt type.
The proof does not assume that the whole fixed pool is eligible. -/
theorem selectedStagePoolPrescribedData_targets_admissible
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (ell : Nat) (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop) :
    ∀ T, T ∈ (selectedStagePoolPrescribedData A ell original Selected).source →
      IsAdmissibleRawType family
        (⟨ell+1,(selectedStagePoolPrescribedData A ell original Selected).target T⟩ :
          RawPartialTypeNode db du dd) := by
  intro T hT
  obtain ⟨v,_hSel,hCut,_hOld,hTarget⟩ :=
    selectedStagePoolPrescribedData_source_original
      A ell original Selected T hT
  rw [hTarget]
  have hOldAd : IsAdmissibleRawType family
      (A.rawTypeAtFree (original v).val) :=
    ⟨A,(original v).val,(original v).isLt,hAvoidA,rfl⟩
  have hPrefix :=
    admissibleRawType_closed_under_prefix
      family hOldAd (ell+1) hCut
  change IsAdmissibleRawType family
    (⟨ell+1,
      (A.partialTypeAt (A.freeLevel (original v).val)
        (original v).val).restrict hCut⟩ :
      RawPartialTypeNode db du dd) at hPrefix
  rw [A.partialTypeAt_restrict
    (ell+1) (A.freeLevel (original v).val) (original v).val hCut]
    at hPrefix
  exact hPrefix

/-- Source records come from one ordinary L+ socle even after
restricting to a level-dependent selection of original names. -/
theorem selectedStagePoolPrescribedData_correctedB3_iff_compatibleB3
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop) :
    (selectedStagePoolPrescribedData A ell original Selected).CorrectedB3 family ↔
      (selectedStagePoolPrescribedData A ell original Selected).CompatibleB3 family := by
  let F := selectedStagePoolPrescribedData A ell original Selected
  have hSource : ∀ T, T ∈ F.source →
      ∃ u : Nat, T = A.partialTypeAt ell u := by
    intro T hT
    obtain ⟨v,_hSelected,_hCut,hOld,_hTarget⟩ :=
      selectedStagePoolPrescribedData_source_original
        A ell original Selected T hT
    exact ⟨(original v).val,hOld⟩
  have hPairwise : ∀ T U, T ∈ F.source → U ∈ F.source →
      SameOrdinaryAtCut T U :=
    F.source_pairwise_compatible_of_ambient A hSource
  exact F.correctedB3_iff_compatibleB3_of_one_socle family hPairwise

/-- A finite L-only B3 witness from the selected graph remembers
both selection and the real cut guard of each upper original.
There is no arbitrary auxiliary E on this witness. -/
theorem selectedStagePool_failedCorrectedB3_has_selected_original_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hEll : ell < A.size)
    (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop)
    (hFailure :
      ¬ (selectedStagePoolPrescribedData
        A ell original Selected).CorrectedB3 family) :
    ∃ S0 : PartialTypeWithE ell db du dd,
      S0 ∈ (selectedStagePoolPrescribedData A ell original Selected).source ∧
      ∃ W : AgeTestModel db du dd,
        W.BoundedCarrier ∧
        SameInitialL W A.L ell ∧
        (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
        (∀ x, x ∈ W.carrier → ell < x →
          ∃ v : Fin M, Selected v ∧
            ell+1 ≤ A.freeLevel (original v).val ∧
            RelationalPrefixType.ofAgeModel W (ell+1) x =
              RelationalPrefixType.ofAgeModel A.L (ell+1)
                (original v).val) ∧
        ∃ bad, bad ∈ family ∧ ¬ bad.Avoids W := by
  classical
  let F := selectedStagePoolPrescribedData A ell original Selected
  have hFailCompatible : ¬ F.CompatibleB3 family := by
    intro hGood
    exact hFailure ((selectedStagePoolPrescribedData_correctedB3_iff_compatibleB3
      family A ell original Selected).2 hGood)
  unfold PrescribedBoringData.CompatibleB3 at hFailCompatible
  push_neg at hFailCompatible
  obtain ⟨S0,hS0,hFailedAge⟩ := hFailCompatible
  obtain ⟨W,hFinite,hSame,hUpper,hDelete,bad,hMember,hBad⟩ :=
    failedCommonSocleAgeTest_has_finite_L_witness
      family (prescribedOrdinarySocle (F.target S0))
      ell (F.CompatibleUpperLType S0) hFailedAge
  have hSameAmbient : SameInitialL W A.L ell := by
    obtain ⟨v,_hSel,_hCut,_hOld,hTarget⟩ :=
      selectedStagePoolPrescribedData_source_original
        A ell original Selected S0 hS0
    have hSocleTarget :
        SameInitialL (prescribedOrdinarySocle (F.target S0))
          A.L ell := by
      rw [hTarget]
      exact ambient_partialType_prescribedSocle
        A ell (original v).val hEll
    exact hSame.trans hSocleTarget
  refine ⟨S0,hS0,W,hFinite,hSameAmbient,hDelete,?_,bad,hMember,hBad⟩
  intro x hx hAbove
  obtain ⟨T,hT,_hCompatible,hType⟩ := hUpper x hx hAbove
  obtain ⟨v,hSel,hCut,_hOld,hTarget⟩ :=
    selectedStagePoolPrescribedData_source_original
      A ell original Selected T hT
  refine ⟨v,hSel,hCut,?_⟩
  have hReduct :
      (F.target T).lReduct =
        RelationalPrefixType.ofAgeModel A.L (ell+1)
          (original v).val := by
    rw [hTarget]
    exact partialTypeAt_lReduct_eq_ofAgeModel
      A (ell+1) (original v).val
  exact hType.trans hReduct

/-- Two prescribed functions with the same source and equal
FULL targets on that source have equivalent corrected finite B3.
In particular, varying the arbitrary target value outside the
source cannot change a test. -/
theorem PrescribedBoringData.correctedB3_iff_of_source_target
    {ell db du dd : Nat}
    (F G : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hSource : ∀ T, T ∈ F.source ↔ T ∈ G.source)
    (hTarget : ∀ T, T ∈ F.source → F.target T = G.target T) :
    F.CorrectedB3 family ↔ G.CorrectedB3 family := by
  constructor
  · intro hF S0 hG0 W hFinite hSameG hUpperG hDelete
    have hF0 : S0 ∈ F.source := (hSource S0).2 hG0
    have hSameF :
        SameInitialL W (prescribedOrdinarySocle (F.target S0)) ell := by
      rw [hTarget S0 hF0]
      exact hSameG
    have hUpperF : UpperTypesPrescribed W ell F.PrescribedUpperLType := by
      intro x hx hAbove
      obtain ⟨T,hGT,hType⟩ := hUpperG x hx hAbove
      have hFT : T ∈ F.source := (hSource T).2 hGT
      refine ⟨T,hFT,?_⟩
      rw [hTarget T hFT]
      exact hType
    exact hF S0 hF0 W hFinite hSameF hUpperF hDelete
  · intro hG S0 hF0 W hFinite hSameF hUpperF hDelete
    have hG0 : S0 ∈ G.source := (hSource S0).1 hF0
    have hSameG :
        SameInitialL W (prescribedOrdinarySocle (G.target S0)) ell := by
      rw [← hTarget S0 hF0]
      exact hSameF
    have hUpperG : UpperTypesPrescribed W ell G.PrescribedUpperLType := by
      intro x hx hAbove
      obtain ⟨T,hFT,hType⟩ := hUpperF x hx hAbove
      have hGT : T ∈ G.source := (hSource T).1 hFT
      refine ⟨T,hGT,?_⟩
      rw [← hTarget T hFT]
      exact hType
    exact hG S0 hG0 W hFinite hSameG hUpperG hDelete

/-- The exact **manuscript-facing** identification criterion.
For the actual closure function f_ell, prove its source is exactly
the selected original types and that it maps every selected old
type to that original's next type.  Then its B3 test is LITERALLY
equivalent to that of the selected finite pool.

Both clauses are essential: merely knowing that all actual source
types are represented in a LARGER eligible ambient pool is not
enough to infer a failed age test for that larger pool. -/
theorem selectedStagePool_B3_iff_of_source_and_graph
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (Selected : Fin M → Prop)
    (F : PrescribedBoringData ell db du dd)
    (hSource : ∀ T,
      T ∈ F.source ↔
        T ∈ (selectedStagePoolPrescribedData
          A ell original Selected).source)
    (hGraph : ∀ v : Fin M, Selected v →
      ell+1 ≤ A.freeLevel (original v).val →
      F.target (A.partialTypeAt ell (original v).val) =
        A.partialTypeAt (ell+1) (original v).val) :
    F.CorrectedB3 family ↔
      (selectedStagePoolPrescribedData A ell original Selected).CorrectedB3 family := by
  apply F.correctedB3_iff_of_source_target
    (selectedStagePoolPrescribedData A ell original Selected) family
    hSource
  intro T hT
  obtain ⟨v,hSelected,hCut,hOld,hNew⟩ :=
    selectedStagePoolPrescribedData_source_original
      A ell original Selected T ((hSource T).1 hT)
  calc
    F.target T = F.target (A.partialTypeAt ell (original v).val) :=
      congrArg F.target hOld
    _ = A.partialTypeAt (ell+1) (original v).val :=
      hGraph v hSelected hCut
    _ = (selectedStagePoolPrescribedData
      A ell original Selected).target T := hNew.symm

end SuccessorTree.V10
