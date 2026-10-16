import SuccessorTree.V10.GPlusHTopTuplePalette
import SuccessorTree.V10.HUniformEnvelopeBound
import Mathlib.Tactic

/-!
# The sharp numerical H+ bound controls actual G+ prefix-tuple colours

The preceding actual HTop tuple theorem bounds the number of colours
by the finite genuine G+ source-representation palette at the exact
selected-level count of a particular Algorithm 5.4 run.

The already kernel-checked normalized Proposition 6.44 bounds that
same count by b(q)=2(q+1+M)+R(M)+1, where M is the exact descending
numerical generation budget. A simple *actual representing-pair*
inclusion gives monotonicity of the genuine bounded palette and
allows us to replace the run-specific height with b(q).

This is a uniform bound for all tuples of selected HTop initial
prefixes inside this finite numerical H+ construction. It is not
yet the original universal K→H+→G+ embedding theorem or a claim that
all induced A-copies are such tuples.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Every genuine strict Kpt pair of height at most b is also
a genuine pair of height at most B. This includes all positive and
absent L+ atoms because the pair and its G+ vertex are unchanged. -/
theorem boundedGPlusTuplePalette_mono
    (family : List (NormalizedForbidden db du dd))
    {b B q : Nat} (h : b ≤ B) :
    boundedGPlusTuplePalette family b q ⊆
      boundedGPlusTuplePalette family B q := by
  intro t ht
  obtain ⟨pairs, rfl⟩ := ht
  refine ⟨(fun i : Fin q =>
    (⟨(pairs i).val, (pairs i).property.trans h⟩ :
      BoundedGPlusRepresentingPair family B)), ?_⟩
  rfl

/-- The actual finite bounded-representation tuple palette has
monotone cardinality, via an injective inclusion of codes. -/
theorem boundedGPlusPaletteIndices_card_mono
    (family : List (NormalizedForbidden db du dd))
    {b B q : Nat} (h : b ≤ B) :
    Fintype.card (boundedGPlusPaletteIndices family b q) ≤
      Fintype.card (boundedGPlusPaletteIndices family B q) := by
  classical
  let lift :
      boundedGPlusPaletteIndices family b q →
        boundedGPlusPaletteIndices family B q :=
    fun e => ⟨e.val,
      boundedGPlusTuplePalette_mono family h e.property⟩
  have hInj : Function.Injective lift := by
    intro e f hef
    have hVal : e.val = f.val :=
      congrArg
        (fun z : boundedGPlusPaletteIndices family B q => z.val) hef
    exact Subtype.ext hVal
  exact Fintype.card_le_of_injective lift hInj

/-- The *actual* Algorithm 5.4 on the numerical HTop seeds gives
one finite-colour bound for ALL selected-prefix q-tuples, in terms
of the SAME explicit v10 numerical budget b(blocks.card), not an
external envelope bound or a run-dependent palette size. -/
theorem numericH_actualRun_topPrefix_tuples_uniform_colour_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ j : Nat, j ∈ blocks →
      hPosition k j k ≤ (finiteNumericH K k N).freeLevel c.val)
    (hStrict : ∀ j : Nat, j ∈ blocks →
      hPosition k j k + 1 ≤ (finiteNumericH K k N).freeLevel c.val)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family)
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin : Set (AdmissibleKptNode family))
      ((finiteNumericH K k N).freeLevel c.val))
    (hFamilyBound : ∀ bad, bad ∈ family →
      bad.patternCard ≤ k+1)
    (q : Nat)
    (χ : (Fin q → FiniteGPlusVertex family) → κ) :
    let M := descendingCumulativeBudget
      (ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard))
      blocks.card (k-1)
    let B := 2*(blocks.card+1+M) +
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M + 1
    ∃ (W : SuccessorTree.SMTree.ShapeSubspace
          (normalizedKptSMTree family) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family B q) ∧
      ∀ t, t ∈ numericHTopPrefixTuples family K k N blocks q →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  classical
  let sizes : Fin family.length → Nat :=
    fun i => (family.get i).patternCard
  let M : Nat :=
    descendingCumulativeBudget (ageSignatureCapacity sizes)
      blocks.card (k-1)
  let B : Nat :=
    2*(blocks.card+1+M) + ageSignatureCapacity sizes M + 1
  have hHeight : R.selectedLevels.card ≤ B := by
    have hBound := numericH_actualRun_uniform_sharp_envelope_bound
      family K hCarrier hAvoidK k N hk
      c blocks hWithin R hFamilyBound
    change R.selectedLevels.card ≤ B at hBound
    exact hBound
  have hPalette :
      Fintype.card
        (boundedGPlusPaletteIndices family R.selectedLevels.card q) ≤
        Fintype.card (boundedGPlusPaletteIndices family B q) :=
    boundedGPlusPaletteIndices_card_mono family hHeight
  obtain ⟨W,colours,hCard,hAll⟩ :=
    numericHTopRun_prefixTuples_finiteColour_bound
      family K k N
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin hStrict R q χ
  exact ⟨W,colours,hCard.trans hPalette,hAll⟩

end SuccessorTree.V10
