import SuccessorTree.V10.GPlusHtopFixedGOmegaBlockTuples
import SuccessorTree.V10.GPlusHTopBudgetMono
import SuccessorTree.EnvelopeRunExistence
import Mathlib.Tactic

/-!
# One genuine finite palette covers every top-generation q-tuple in fixed Gω

The quantifiers matter: each finite tuple chooses its own finitely many
numerical top blocks, later top root and actual finite Algorithm 5.4 run,
but the SHARP height bound depends only on q. Enlarge each of those
finite-approximation factorizations to the SAME b(q), where
  b(q)=2(q+1+M(q))+R(M(q))+1.
The resulting genuine `FiniteGPlusPaletteCovers` quantifies over *all*
top-generation tuples BEFORE applying the finite shape-Ramsey theorem.

Every image is computed in one fixed exhaustive size-ordered Gω.
The chosen numerical H+ and its finite H+ code agree exactly, including
positive and absent directed binary, unary, diagonal and E atoms.

This closes the key infinite-quantifier/palette-factorization gap of
normalized Section 6. The remaining author-language adapter and exact
end-to-end big Ramsey theorem are stated separately.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- The complete family of ALL tuples from the fixed-Gω embedded
top-generation copy of K. Not a prescribed finite set of blocks or
a tuple-dependent target set. -/
def numericKFixedGOmegaTopTuples
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k q : Nat) :
    Set (Fin q → FiniteGPlusVertex family) :=
  Set.range (fun indices : Fin q → Nat =>
    fun i : Fin q =>
      GPlusEnumeration.enumerate C family hAvoidC
        ((infiniteNumericHPlus K k).toGOmega family
          (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)
          (hPosition k (indices i) k)))

/-- The whole infinite family of top-generation q-tuples factors through
ONE finite genuine bounded Kpt palette, with the SHARP numerical
height b(q) independent of the tuple and of its chosen top root.

Each individual tuple uses one finite H+ construction and AlgorithmRun
to find its real finite AM representative. Monotone complete-palette
coverage then puts all such representations into the SAME bound b(q)
before applying the single shape Ramsey theorem. -/
theorem numericKFixedGOmegaTopTuples_uniform_palette_cover
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) (hk : 0 < k)
    (hFamilyBound : ∀ bad, bad ∈ family → bad.patternCard ≤ k+1)
    (q : Nat) :
    FiniteGPlusPaletteCovers family
      (numericHTopUniformPaletteHeight family k q) q
      (numericKFixedGOmegaTopTuples
        family C hAvoidC K hCarrier hAvoidK k q) := by
  classical
  intro t ht
  obtain ⟨indices, rfl⟩ := ht
  obtain ⟨blocks, j, hCard, hj, hIndices, hEarlier⟩ :=
    numericHTop_indices_common_later_root indices
  let N : Nat := hPosition k j k + 1
  obtain ⟨c, _hc, hStrictRoot⟩ :=
    finiteNumericH_top_root_for_earlier_blocks_strict
      K k j hk hj blocks hEarlier
  have hStrict : ∀ i : Nat, i ∈ blocks →
      hPosition k i k + 1 ≤
        (finiteNumericH K k N).freeLevel c.val := by
    intro i hi
    simpa only [N] using hStrictRoot i hi
  have hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤
        (finiteNumericH K k N).freeLevel c.val := by
    intro i hi
    have hs := hStrict i hi
    omega
  let hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N) :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N
      hAvoidH c blocks hWithin
  let H := normalizedKptSMTree family
  let R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      H X ((finiteNumericH K k N).freeLevel c.val) :=
    SuccessorTree.SMTree.Envelope.canonicalAlgorithmRun
      H X ((finiteNumericH K k N).freeLevel c.val)
  have hRunHeight :
      R.selectedLevels.card ≤
        numericHTopUniformPaletteHeight family k blocks.card := by
    have hSharp := numericH_actualRun_uniform_sharp_envelope_bound
      family K hCarrier hAvoidK k N hk c blocks hWithin R hFamilyBound
    change R.selectedLevels.card ≤
      numericHTopUniformPaletteHeight family k blocks.card at hSharp
    exact hSharp
  have hUniform :
      R.selectedLevels.card ≤
        numericHTopUniformPaletteHeight family k q :=
    hRunHeight.trans
      (numericHTopUniformPaletteHeight_mono_q family k hCard)
  have hLocal :
      FiniteGPlusPaletteCovers family R.selectedLevels.card q
        (numericHTopPrefixTuples family K k N blocks q) :=
    numericHTopRun_prefixTuples_finiteApprox_cover
      family K k N hAvoidH c blocks hWithin hStrict R q
  have hUniformCover :
      FiniteGPlusPaletteCovers family
        (numericHTopUniformPaletteHeight family k q) q
        (numericHTopPrefixTuples family K k N blocks q) :=
    finiteGPlusPaletteCovers_mono family hUniform
      (numericHTopPrefixTuples family K k N blocks q) hLocal
  have hMember :
      (fun i : Fin q =>
        GPlusEnumeration.enumerate C family hAvoidC
          ((infiniteNumericHPlus K k).toGOmega family
            (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)
            (hPosition k (indices i) k))) ∈
        numericHTopPrefixTuples family K k N blocks q := by
    change (fun i : Fin q =>
        GPlusEnumeration.enumerate C family hAvoidC
          ((infiniteNumericHPlus K k).toGOmega family
            (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)
            (hPosition k (indices i) k))) ∈
        numericHTopPrefixTuples family K k (hPosition k j k + 1)
          blocks q
    exact numericHTop_fixedGOmega_tuple_mem_prefixTuples
      family C hAvoidC K hCarrier hAvoidK
      k j q blocks hEarlier indices hIndices
  exact hUniformCover _ hMember

/-- One Ramsey subspace, not one subspace per tuple, bounds every
top-generation q-tuple of the fixed ordered universal Gω. The bound
is exactly the genuine finite Kpt source-palette cardinal at b(q). -/
theorem numericKFixedGOmegaTopTuples_uniform_colour_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) (hk : 0 < k)
    (hFamilyBound : ∀ bad, bad ∈ family → bad.patternCard ≤ k+1)
    (q : Nat)
    (χ : (Fin q → FiniteGPlusVertex family) → κ) :
    ∃ (W : SuccessorTree.SMTree.ShapeSubspace
          (normalizedKptSMTree family) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family k q) q) ∧
      ∀ t, t ∈ numericKFixedGOmegaTopTuples
          family C hAvoidC K hCarrier hAvoidK k q →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  exact normalizedKpt_GPlus_finite_colour_bound_of_cover
    family (numericHTopUniformPaletteHeight family k q) q
    (numericKFixedGOmegaTopTuples
      family C hAvoidC K hCarrier hAvoidK k q) χ
    (numericKFixedGOmegaTopTuples_uniform_palette_cover
      family C hAvoidC K hCarrier hAvoidK k hk hFamilyBound q)

end SuccessorTree.V10
