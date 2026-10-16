import SuccessorTree.V10.KptBigRamseyNormalizedTheorem
import SuccessorTree.V10.BinaryUnaryAgeAdapter
import Mathlib.Tactic

/-!
# Author-language finite unary/binary copy colourings

For an ordinary finite relational signature of unary and binary
predicates, the binary diagonal B(x,x,r) is genuine singleton data,
not an off-diagonal relation. The existing normalized AgeTestModel
stores these bits in a separate field. This file closes the
paper-to-Lean copy/colour adapter rather than asserting a new
equivalence by fiat.

Define the genuine original-language binary relation of a normalized
model using its directed binary field for distinct vertices and its
diagonal field for equal vertices. A finite original-language
induced copy then means a strictly increasing enumerated map
preserving *all* unary and *all* binary atoms, including both
directions, loops and absent facts.

The exact iff with the already checked normalized Realizes predicate
turns the final normalized Gω theorem into the explicit finite
unary/binary pattern-colouring big Ramsey statement. The selected
neutral singleton normalization was independently proved in
SingletonNormalization; no new E relation is invented.
-/

namespace SuccessorTree.V10

variable {db du : Nat}

/-- The original binary relation includes diagonal loops of binary
symbols. All distinct directed atoms are read verbatim from the
normalized off-diagonal table. -/
def AgeTestModel.originalBinary
    (G : AgeTestModel db du db)
    (x y : Nat) (t : Fin db) : Bool :=
  if x = y then G.diagonal x t else G.binary x y t

/-- Exact original unary/binary induced ordered copies, including
arbitrary absent relations and binary loops. -/
def binaryUnaryInducedCopies
    {q : Nat}
    (G : AgeTestModel db du db)
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool) :
    Set (Fin q → Nat) :=
  {f | StrictMono f ∧
      (∀ a : Fin q, f a ∈ G.carrier) ∧
      (∀ a b : Fin q, ∀ t : Fin db,
        G.originalBinary (f a) (f b) t = PB a b t) ∧
      (∀ a : Fin q, ∀ t : Fin du, G.unary (f a) t = PU a t)}

/-- The original-language and normalized predicates define exactly
the SAME induced ordered copies, both positive and absent atoms.
For different a,b use the binary field; for a=b use the actual
diagonal field (not the unused normalized binary diagonal). -/
theorem binaryUnary_originalCopy_iff_normalized
    {q : Nat}
    (G : AgeTestModel db du db)
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool)
    (f : Fin q → Nat) :
    G.Realizes (binaryUnaryForbiddenPattern PB PU) f ↔
      f ∈ binaryUnaryInducedCopies G PB PU := by
  constructor
  · rintro ⟨hMono, hCarrier, hBinary, hUnary, hDiagonal⟩
    change StrictMono f ∧
      (∀ a : Fin q, f a ∈ G.carrier) ∧
      (∀ a b : Fin q, ∀ t : Fin db,
        G.originalBinary (f a) (f b) t = PB a b t) ∧
      (∀ a : Fin q, ∀ t : Fin du, G.unary (f a) t = PU a t)
    refine ⟨hMono, hCarrier, ?_, hUnary⟩
    intro a b t
    by_cases hab : a = b
    · subst b
      simpa [AgeTestModel.originalBinary, binaryUnaryForbiddenPattern] using hDiagonal a t
    · have hfne : f a ≠ f b :=
        fun heq => hab (hMono.injective heq)
      simpa [AgeTestModel.originalBinary, binaryUnaryForbiddenPattern, hfne] using
        hBinary a b hab t
  · rintro ⟨hMono, hCarrier, hOriginal, hUnary⟩
    refine ⟨hMono, hCarrier, ?_, hUnary, ?_⟩
    · intro a b hab t
      have hfne : f a ≠ f b :=
        fun heq => hab (hMono.injective heq)
      simpa [AgeTestModel.originalBinary, binaryUnaryForbiddenPattern, hfne] using
        hOriginal a b t
    · intro a t
      simpa [AgeTestModel.originalBinary, binaryUnaryForbiddenPattern] using hOriginal a a t

/-- The literal original finite unary/binary induced-pattern colouring
theorem for the SAME fixed Gω. Copies are not assumed to be just
positive homomorphisms: they include every negative atom, directed
tuple and diagonal loop. The universal order is its actual
size-respecting enumeration order.

An induced copy of a finite A with q vertices is one of the above
maps; the resulting self-embedding and palette bound work for every
finite colouring of such copies. -/
theorem originalBinaryUnary_GOmega_pattern_bigRamsey_bound
    {κ : Type*} [Fintype κ] [Inhabited κ]
    (family : List (NormalizedForbidden db du db))
    (C : CountableEnumeratedPartialStructure db du db)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    {q : Nat}
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool)
    (χ : {f : Fin q → Nat //
      f ∈ binaryUnaryInducedCopies
        (finiteGPlusEnumeratedL
          (GPlusEnumeration.enumerate C family hAvoidC)) PB PU} → κ) :
    let E := GPlusEnumeration.enumerate C family hAvoidC
    let G := finiteGPlusEnumeratedL E
    ∃ (e : G.InducedEmbedding G)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ (f : Fin q → Nat)
        (hf : f ∈ binaryUnaryInducedCopies G PB PU),
        ∃ hImage : (fun i => e.toFun (f i)) ∈
            binaryUnaryInducedCopies G PB PU,
          χ ⟨(fun i => e.toFun (f i)), hImage⟩ ∈ colours := by
  classical
  let E := GPlusEnumeration.enumerate C family hAvoidC
  let G : AgeTestModel db du db := finiteGPlusEnumeratedL E
  let P : ForbiddenAtomicPattern q db du db :=
    binaryUnaryForbiddenPattern PB PU
  have hCopies (f : Fin q → Nat) :
      G.Realizes P f ↔ f ∈ binaryUnaryInducedCopies G PB PU :=
    binaryUnary_originalCopy_iff_normalized G PB PU f
  let χNormalized : {f : Fin q → Nat // G.Realizes P f} → κ :=
    fun f => χ ⟨f.val, (hCopies f.val).mp f.property⟩
  obtain ⟨e, colours, hCard, hAll⟩ :=
    normalizedKpt_GOmega_pattern_bigRamsey_bound
      family C hAvoidC P χNormalized
  refine ⟨e,colours,hCard,?_⟩
  intro f hf
  have hNorm : G.Realizes P f := (hCopies f).mpr hf
  have hNormImage : G.Realizes P (fun i => e.toFun (f i)) :=
    e.realizes P f hNorm
  let hImage : (fun i => e.toFun (f i)) ∈
      binaryUnaryInducedCopies G PB PU :=
    (hCopies _).mp hNormImage
  refine ⟨hImage, ?_⟩
  have hColour := hAll f hNorm
  change χNormalized ⟨(fun i => e.toFun (f i)), hNormImage⟩ ∈
    colours at hColour
  exact hColour


/-!
## Unordered embeddings: Definition 6.25 colours Emb(A,K), not OEmb(A,K)

An embedding of a finite enumerated pattern need not respect its
enumeration order. The final tuple theorem already covers arbitrary
tuples. We therefore also make the actual (not necessarily monotone)
induced-embedding predicate explicit and transport its copy
colourings without restricting them to ordered embeddings.
-/

/-- The ORIGINAL induced embeddings of an arbitrary finite unary/
binary pattern, without demanding the map itself be increasing.
The K order remains present on the target but is not part of
the finite-structure embedding predicate of Definition 6.25. -/
def binaryUnaryAllEmbeddings
    {q : Nat}
    (G : AgeTestModel db du db)
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool) :
    Set (Fin q → Nat) :=
  {f | Function.Injective f ∧
      (∀ a : Fin q, f a ∈ G.carrier) ∧
      (∀ a b : Fin q, ∀ t : Fin db,
        G.originalBinary (f a) (f b) t = PB a b t) ∧
      (∀ a : Fin q, ∀ t : Fin du, G.unary (f a) t = PU a t)}

/-- Any ordered induced embedding of the ambient countable models
takes a genuine finite, possibly UNORDERED source embedding to
another genuine finite embedding. This preserves every positive
and negative unary, directed binary and diagonal binary-loop bit. -/
theorem binaryUnaryAllEmbeddings_preserved
    {q : Nat}
    (G H : AgeTestModel db du db)
    (e : G.InducedEmbedding H)
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool)
    (f : Fin q → Nat)
    (hf : f ∈ binaryUnaryAllEmbeddings G PB PU) :
    (fun a => e.toFun (f a)) ∈
      binaryUnaryAllEmbeddings H PB PU := by
  rcases hf with ⟨hInjective,hCarrier,hBinary,hUnary⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro a b heq
    exact hInjective (e.strictMono.injective heq)
  · intro a
    exact e.inside (f a) (hCarrier a)
  · intro a b t
    by_cases hab : a = b
    · subst b
      change H.diagonal (e.toFun (f a)) t = PB a a t
      calc
        H.diagonal (e.toFun (f a)) t =
            G.diagonal (f a) t :=
          e.diagonal (f a) (hCarrier a) t
        _ = PB a a t := by
          simpa [AgeTestModel.originalBinary] using hBinary a a t
    · have hDifferent : f a ≠ f b := by
        intro heq
        exact hab (hInjective heq)
      have hImageDifferent :
          e.toFun (f a) ≠ e.toFun (f b) := by
        intro heq
        exact hDifferent (e.strictMono.injective heq)
      have hOldBinary :
          G.binary (f a) (f b) t = PB a b t := by
        simpa [AgeTestModel.originalBinary, hDifferent] using
          hBinary a b t
      have hNewBinary :
          H.binary (e.toFun (f a)) (e.toFun (f b)) t =
            PB a b t :=
        (e.binary (f a) (f b) (hCarrier a) (hCarrier b)
          hDifferent t).trans hOldBinary
      simpa [AgeTestModel.originalBinary,hImageDifferent] using
        hNewBinary
  · intro a t
    exact (e.unary (f a) (hCarrier a) t).trans (hUnary a t)

/-- The exact Definition 6.25 BIG Ramsey conclusion for **all**
induced embeddings of a finite original unary/binary pattern in
the fixed Gω, not only its order-preserving enumerations.

The embedding e of the universal target is itself ordered;
the finite coloured embeddings f may be arbitrary injective
structure embeddings. One e controls ALL of them simultaneously. -/
theorem originalBinaryUnary_GOmega_allEmbeddings_bigRamsey_bound
    {κ : Type*} [Fintype κ] [Inhabited κ]
    (family : List (NormalizedForbidden db du db))
    (C : CountableEnumeratedPartialStructure db du db)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    {q : Nat}
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool)
    (χ : {f : Fin q → Nat //
      f ∈ binaryUnaryAllEmbeddings
        (finiteGPlusEnumeratedL
          (GPlusEnumeration.enumerate C family hAvoidC)) PB PU} → κ) :
    let E := GPlusEnumeration.enumerate C family hAvoidC
    let G := finiteGPlusEnumeratedL E
    ∃ (e : G.InducedEmbedding G)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family
            (normalizedKptGeneration family) q) q) ∧
      ∀ (f : Fin q → Nat)
        (hf : f ∈ binaryUnaryAllEmbeddings G PB PU),
        ∃ hImage : (fun i => e.toFun (f i)) ∈
            binaryUnaryAllEmbeddings G PB PU,
          χ ⟨(fun i => e.toFun (f i)), hImage⟩ ∈ colours := by
  classical
  let E := GPlusEnumeration.enumerate C family hAvoidC
  let G : AgeTestModel db du db := finiteGPlusEnumeratedL E
  let χFull : (Fin q → Nat) → κ :=
    fun f => if h : f ∈ binaryUnaryAllEmbeddings G PB PU
      then χ ⟨f,h⟩ else default
  obtain ⟨e,colours,hCard,hAll⟩ :=
    normalizedKpt_GOmega_self_bigRamsey_bound
      family C hAvoidC q χFull
  refine ⟨e,colours,hCard,?_⟩
  intro f hf
  have hImage :
      (fun i => e.toFun (f i)) ∈
        binaryUnaryAllEmbeddings G PB PU :=
    binaryUnaryAllEmbeddings_preserved G G e PB PU f hf
  refine ⟨hImage,?_⟩
  have hColour := hAll f
  change χFull (fun i => e.toFun (f i)) ∈ colours at hColour
  simpa only [χFull,dif_pos hImage] using hColour

end SuccessorTree.V10
