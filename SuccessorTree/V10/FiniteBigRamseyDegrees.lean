import SuccessorTree.V10.KptUniversalAgeBigRamsey

/-!
# Finite big Ramsey degrees: a paper-facing predicate

The source paper's Definition 6.25 quantifies over *all* embeddings
of every finite substructure, not only the embeddings preserving the
enumeration of its domain. Our finite pattern consists of the full
directed binary table (including diagonal entries) and unary table,
and an embedding is an injective induced map of those records.

This file packages the already-verified explicit colour bound into a
single predicate expressing finite big Ramsey degrees. Using
`Fin (r + 1)` for finite colourings avoids requiring a separately
inhabited general finite colour type. The bound depends only on the
finite source size and normalized forbidden family, not on the
particular finite pattern or colouring.

The underlying theorem is `universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound`.
No extra combinatorial hypothesis, axiom or model constructor is added.
-/

namespace SuccessorTree.V10

/-- An explicit uniform bound for all `q`-vertex induced unary/binary
patterns in the normalized forbidden age. -/
noncomputable def normalizedOriginalBigRamseyBound
    {db du : Nat}
    (family : List (NormalizedForbidden db du db))
    (q : Nat) : Nat :=
  Fintype.card
    (boundedGPlusPaletteIndices family
      (numericHTopUniformPaletteHeight family
        (normalizedKptGeneration family) q) q)

/-- The `Emb(A,K)` (not just `OEmb(A,K)`) formulation of finite
big Ramsey degrees for countable unary/binary relational structures.
The quantification over all finite relation tables is harmless even
when some patterns have no embeddings into `K`. -/
def AgeTestModel.HasOriginalFiniteBigRamseyDegrees
    {db du : Nat} (K : AgeTestModel db du db) : Prop :=
  ∀ (q : Nat)
    (PB : Fin q → Fin q → Fin db → Bool)
    (PU : Fin q → Fin du → Bool),
    ∃ t : Nat,
      ∀ (r : Nat)
        (χ : {f : Fin q → Nat //
          f ∈ binaryUnaryAllEmbeddings K PB PU} → Fin (r + 1)),
        ∃ (e : K.InducedEmbedding K)
          (colours : Finset (Fin (r + 1))),
          colours.card ≤ t ∧
          ∀ (f : Fin q → Nat)
            (hf : f ∈ binaryUnaryAllEmbeddings K PB PU),
            ∃ hImage :
              (fun i => e.toFun (f i)) ∈
                binaryUnaryAllEmbeddings K PB PU,
              χ ⟨(fun i => e.toFun (f i)), hImage⟩ ∈ colours

/-- Every countable full-carrier age-universal model of the normalized
finite irreducible unary/binary forbidden age has finite big Ramsey
degrees for **all** induced embeddings of every finite pattern.

This is Definition 6.25 / Theorem 6.26 at the precise normalized
`AgeTestModel` and `NormalizedForbidden` interfaces. The
interpretation of the manuscript's original age and its Fraïssé
universality remains a separate statement-correspondence check. -/
theorem AgeTestModel.hasOriginalFiniteBigRamseyDegrees_of_universal
    {db du : Nat}
    (family : List (NormalizedForbidden db du db))
    (K : AgeTestModel db du db)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (hUniversal : K.UniversalForNormalizedFamily family) :
    K.HasOriginalFiniteBigRamseyDegrees := by
  intro q PB PU
  refine ⟨normalizedOriginalBigRamseyBound family q, ?_⟩
  intro r χ
  simpa only [normalizedOriginalBigRamseyBound] using
    (universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound
      (κ := Fin (r + 1)) family K
      hCarrier hAvoidK hUniversal PB PU χ)

end SuccessorTree.V10
