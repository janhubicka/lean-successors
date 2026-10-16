import SuccessorTree.V10.KptFinalBigRamseyTransfer
import Mathlib.Tactic

/-!
# Uniform normalized big Ramsey theorem without a hand-supplied generation

The finite forbidden signature is an actual finite List. Its largest
forbidden pattern size is therefore bounded. Choose the generation k
once from this list, ensuring k>0 even when the family is empty.

The previously checked finite H+ numerical construction then proves
the big Ramsey bound with NO user-supplied numerical generation, no
family cardinality assumption, no abstract E1 hypothesis, no
tuple-dependent shape subspace, and no tuple-dependent finite palette.

The target is ONE fixed exhaustive Gω of the finite L+ codes, whose
existence only requires a countable forbidden-free partial structure
to witness each finite code layer is inhabited. In particular, Gω
itself has bounded big Ramsey degrees for every finite ordered
induced pattern in the normalized finite unary/directed-binary/
diagonal signature.

The chosen generation is deliberately an upper bound, not claimed to
be optimal. Author-language equivalence and separately stated
boundary conventions are documented as different interfaces.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- A concrete positive generation large enough for every forbidden
pattern in the finite normalized family, including the empty family.
There are no extra assumptions about the forbidden family. -/
noncomputable def normalizedKptGeneration
    (family : List (NormalizedForbidden db du dd)) : Nat := by
  classical
  exact max 1
    (family.toFinset.sup
      (fun bad : NormalizedForbidden db du dd => bad.patternCard))

theorem normalizedKptGeneration_pos
    (family : List (NormalizedForbidden db du dd)) :
    0 < normalizedKptGeneration family := by
  unfold normalizedKptGeneration
  omega

theorem normalizedKptGeneration_bounds_family
    (family : List (NormalizedForbidden db du dd)) :
    ∀ bad, bad ∈ family →
      bad.patternCard ≤ normalizedKptGeneration family + 1 := by
  classical
  intro bad hBad
  have hMem : bad ∈ family.toFinset := by simpa using hBad
  have hSup : bad.patternCard ≤
      family.toFinset.sup
        (fun b : NormalizedForbidden db du dd => b.patternCard) :=
    Finset.le_sup hMem
  unfold normalizedKptGeneration
  omega

/-- The normalized finite-signature big Ramsey theorem with *only*
the genuine age hypotheses. The numerical generation and the
concrete uniform finite G+ palette depend on the finite forbidden
family and q, and NOT on K or the colouring. -/
theorem normalizedKpt_bigRamsey_bound_fixedGOmega
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (q : Nat) (χ : (Fin q → Nat) → κ) :
    ∃ (e : K.InducedEmbedding
          (finiteGPlusEnumeratedL
            (GPlusEnumeration.enumerate C family hAvoidC)))
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ indices : Fin q → Nat,
        χ (fun i => e.toFun (indices i)) ∈ colours := by
  exact normalizedKpt_fixedGOmega_finite_bigRamsey_transfer
    family C hAvoidC K hCarrier hAvoidK
    (normalizedKptGeneration family)
    (normalizedKptGeneration_pos family)
    (normalizedKptGeneration_bounds_family family)
    q χ

/-- The actual fixed Gω, with its already proved size-respecting
exhaustive enumeration, has a finite big Ramsey degree for
*every* finite ordered pattern size q. The conclusion is stronger
than needed: the colour bound holds simultaneously on ALL q-tuples,
not just the tuples representing copies of one finite A. -/
theorem normalizedKpt_GOmega_self_bigRamsey_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (q : Nat) (χ : (Fin q → Nat) → κ) :
    let E := GPlusEnumeration.enumerate C family hAvoidC
    let G := finiteGPlusEnumeratedL E
    ∃ (e : G.InducedEmbedding G)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ indices : Fin q → Nat,
        χ (fun i => e.toFun (indices i)) ∈ colours := by
  let E := GPlusEnumeration.enumerate C family hAvoidC
  let G : AgeTestModel db du dd := finiteGPlusEnumeratedL E
  have hCarrier : ∀ i, i ∈ G.carrier := by
    intro i
    trivial
  have hAvoidG : ∀ bad, bad ∈ family → bad.Avoids G :=
    GPlusEnumeration.enumeratedL_avoids_family C family hAvoidC
  exact normalizedKpt_bigRamsey_bound_fixedGOmega
    family C hAvoidC G hCarrier hAvoidG q χ

/-- Explicit restriction to copies of a particular finite ordered
induced normalized pattern P. This uses only the already verified
induced-embedding transport of complete positive AND absent atoms.
The source is the same fixed Gω; no new copy predicate is assumed. -/
theorem normalizedKpt_GOmega_pattern_bigRamsey_bound
    {κ : Type*} [Fintype κ] [Inhabited κ]
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    {q : Nat} (P : ForbiddenAtomicPattern q db du dd)
    (χ : {indices : Fin q → Nat //
      (finiteGPlusEnumeratedL
        (GPlusEnumeration.enumerate C family hAvoidC)).Realizes
          P indices} → κ) :
    let E := GPlusEnumeration.enumerate C family hAvoidC
    let G := finiteGPlusEnumeratedL E
    ∃ (e : G.InducedEmbedding G)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ (indices : Fin q → Nat)
        (hCopy : G.Realizes P indices),
        χ ⟨(fun i => e.toFun (indices i)), e.realizes P indices hCopy⟩ ∈
          colours := by
  classical
  let E := GPlusEnumeration.enumerate C family hAvoidC
  let G : AgeTestModel db du dd := finiteGPlusEnumeratedL E
  let χFull : (Fin q → Nat) → κ :=
    fun indices =>
      if h : G.Realizes P indices then χ ⟨indices,h⟩ else default
  obtain ⟨e, colours, hCard, hAll⟩ :=
    normalizedKpt_GOmega_self_bigRamsey_bound
      family C hAvoidC q χFull
  refine ⟨e,colours,hCard,?_⟩
  intro indices hCopy
  have hImageCopy :
      G.Realizes P (fun i => e.toFun (indices i)) :=
    e.realizes P indices hCopy
  have hCol := hAll indices
  change χFull (fun i => e.toFun (indices i)) ∈ colours at hCol
  simpa only [χFull, dif_pos hImageCopy] using hCol

end SuccessorTree.V10
