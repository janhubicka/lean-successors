import SuccessorTree.V10.KptCanonicalGomegaBigRamsey
import Mathlib.Tactic

/-!
# Finite big Ramsey degrees in every countable universal model of the age

The normalized Section 6 argument constructs one explicit countable
ordered age-universal model Gω with finite big Ramsey degrees. The
paper's final target is usually a fixed Fraïssé limit K_F rather than
this convenient code enumeration.

For any countable full-carrier model K of the same forbidden age,
universality of K supplies an ordered induced embedding Gω→K.
The verified normalized theorem supplies K→Gω reducing each finite
tuple colouring after pulling it back along Gω→K. Composition gives
a genuine K→K self-embedding with the SAME finite big Ramsey bound.

This is the ordinary cofinal-universality transfer. The hypothesis
is a concrete embedding of the explicitly constructed Gω into K,
not an abstract unverified Ramsey or E1 axiom. A usual universal
countable Fraïssé limit satisfies it by the defining universality
property. No homogeneity requirement is used at this last step.

This theorem quantifies over all q-tuples, so it implies the desired
finite degree for every q-vertex induced ordered original-language
structure after the verified unary/binary copy-language adapter.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Explicit one-way age-universality of a fixed countable ordered
model K. The domain W ranges over exactly the full-carrier
forbidden-free countable AgeTestModels handled by v10. This is the
standard countable universality condition, not a Ramsey premise. -/
def AgeTestModel.UniversalForNormalizedFamily
    (K : AgeTestModel db du dd)
    (family : List (NormalizedForbidden db du dd)) : Prop :=
  ∀ W : AgeTestModel db du dd,
    (∀ i, i ∈ W.carrier) →
    (∀ bad, bad ∈ family → bad.Avoids W) →
    Nonempty (W.InducedEmbedding K)

/-- The canonical age-universal Gω is an honest countable full
carrier forbidden-free model and hence embeds into any model
satisfying the standard age-universality interface. -/
theorem universalNormalizedModel_contains_canonicalGOmega
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hUniversal : K.UniversalForNormalizedFamily family) :
    Nonempty
      ((finiteGPlusEnumeratedL
        (canonicalNormalizedGOmegaEnumeration family)).InducedEmbedding K) := by
  let G : AgeTestModel db du dd :=
    finiteGPlusEnumeratedL (canonicalNormalizedGOmegaEnumeration family)
  have hFull : ∀ i, i ∈ G.carrier := by
    intro i
    trivial
  have hAvoid :
      ∀ bad, bad ∈ family → bad.Avoids G :=
    canonicalNormalizedGOmega_avoids_family family
  exact hUniversal G hFull hAvoid

/-- The full universal-age normalized big Ramsey theorem. For
every countable full-carrier forbidden-free age-universal K, every
finite q and every finite colouring of its ordered q-tuples, one
strictly ordered induced *self-embedding K→K* uses at most the
genuine bounded-palette number of colours depending only on
the finite forbidden family and q.

In particular K may be the ordinary countable Fraïssé limit.
No assumption that an arbitrary same-sized G+ enumeration layer
is order-preserved by the shape action is made: that issue was
discharged in the genuine top-generation embedding theorem. -/
theorem universalNormalizedModel_bigRamsey_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (hUniversal : K.UniversalForNormalizedFamily family)
    (q : Nat) (χ : (Fin q → Nat) → κ) :
    ∃ (e : K.InducedEmbedding K)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ indices : Fin q → Nat,
        χ (fun i => e.toFun (indices i)) ∈ colours := by
  classical
  let C := allFalseCountablePartialStructure db du dd
  let hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L :=
    allFalseAgeModel_avoids_family family
  let G : AgeTestModel db du dd :=
    finiteGPlusEnumeratedL (canonicalNormalizedGOmegaEnumeration family)
  obtain ⟨embedG : G.InducedEmbedding K⟩ :=
    universalNormalizedModel_contains_canonicalGOmega family K hUniversal
  let χG : (Fin q → Nat) → κ :=
    fun indices => χ (fun i => embedG.toFun (indices i))
  obtain ⟨embedK, colours, hCard, hAll⟩ :=
    normalizedKpt_bigRamsey_bound_fixedGOmega
      family C hAvoidC K hCarrier hAvoidK q χG
  let e : K.InducedEmbedding K := embedG.comp embedK
  refine ⟨e, colours, hCard, ?_⟩
  intro indices
  exact hAll indices


/-- **Theorem 6.26 in the exact original Emb(A,K) formulation** for
finite unary/binary languages and normalized finite irreducible
forbidden families. The target K is countable, full-carrier,
forbidden-free and age-universal.

The coloured maps are ALL injective induced binary/unary embeddings
of A, not just order-preserving OEmb(A,K); their tuples may enumerate
vertices in any order. The resulting K self-embedding is genuinely
strictly ordered and induced. The finite degree depends only on
the forbidden family and |A|, never on the colouring or choice of
universal K. -/
theorem universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound
    {db du : Nat}
    {κ : Type*} [Fintype κ] [Inhabited κ]
    (family : List (NormalizedForbidden db du db))
    (K : AgeTestModel db du db)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (hUniversal : K.UniversalForNormalizedFamily family)
    {q : Nat}
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool)
    (χ : {f : Fin q → Nat //
      f ∈ binaryUnaryAllEmbeddings K PB PU} → κ) :
    ∃ (e : K.InducedEmbedding K)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ (f : Fin q → Nat)
        (hf : f ∈ binaryUnaryAllEmbeddings K PB PU),
        ∃ hImage : (fun i => e.toFun (f i)) ∈
            binaryUnaryAllEmbeddings K PB PU,
          χ ⟨(fun i => e.toFun (f i)), hImage⟩ ∈ colours := by
  classical
  let χFull : (Fin q → Nat) → κ :=
    fun f => if h : f ∈ binaryUnaryAllEmbeddings K PB PU
      then χ ⟨f,h⟩ else default
  obtain ⟨e,colours,hCard,hAll⟩ :=
    universalNormalizedModel_bigRamsey_bound
      family K hCarrier hAvoidK hUniversal q χFull
  refine ⟨e,colours,hCard,?_⟩
  intro f hf
  have hImage :
      (fun i => e.toFun (f i)) ∈
        binaryUnaryAllEmbeddings K PB PU :=
    binaryUnaryAllEmbeddings_preserved K K e PB PU f hf
  refine ⟨hImage,?_⟩
  have hColour := hAll f
  change χFull (fun i => e.toFun (f i)) ∈ colours at hColour
  simpa only [χFull,dif_pos hImage] using hColour

end SuccessorTree.V10
