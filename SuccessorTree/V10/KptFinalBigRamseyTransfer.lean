import SuccessorTree.V10.GPlusGlobalTopTuplePalette
import SuccessorTree.V10.GPlusInducedAction
import SuccessorTree.V10.GPlusShapeImagePrefix
import Mathlib.Tactic

/-!
# Final normalized big Ramsey transfer into one fixed enumerated Gω

There are two separate questions in the last step of the v10 proof.

1. The finite palette theorem supplies ONE Kpt ShapeSubspace W and ONE
   finite colour set for every q-tuple of the embedded top-generation K.
2. The map obtained by applying the genuine G+ action of W to the
   top-generation K must remain an ORDERED induced L-embedding into
   the same exhaustive size-nondecreasing enumeration Gω.

The second point is not automatic for arbitrary G+ vertices: equal-size
vertices have arbitrary enumeration tie breaks. For the top-generation
copy, however, source code sizes are strictly increasing in K's order.
Every Kpt ShapeMap sends strictly increasing code sizes to strictly
increasing image sizes. Consequently applying the inverse exhaustive
enumeration to the image codes yields an ordered induced embedding.

Composing this real embedding with the verified global palette
stabilization gives a finite colour bound valid SIMULTANEOUSLY for
every q-tuple of its vertices (hence for every induced copy of an
individual q-vertex ordered L-structure).

The endpoint is the FULL normalized Boolean unary/directed-binary/
diagonal finite-forbidden-family big Ramsey transfer at the stated
positive generation and pattern-size hypotheses. The original
author-language adapter and harmless size conventions are separate.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Applying a genuine Kpt ShapeMap to the numerical top-generation
K-embedding and re-enumerating in one fixed Gω gives an actual
strictly ORDERED and induced L-embedding. No order preservation is
postulated for same-size incomparable G+ codes. -/
noncomputable def numericKToFixedGOmega_after_shape
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    K.InducedEmbedding
      (finiteGPlusEnumeratedL (GPlusEnumeration.enumerate C family hAvoidC)) := by
  classical
  let H := infiniteNumericHPlus K k
  let hAvoidH : ∀ bad, bad ∈ family → bad.Avoids H.L :=
    infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
  let E := GPlusEnumeration.enumerate C family hAvoidC
  let rank : Nat → Nat :=
    fun i => H.toGOmega family hAvoidH (hPosition k i k)
  let source : Nat → FiniteGPlusVertex family :=
    fun i => E (rank i)
  let targetRank : Nat → Nat :=
    fun i => E.symm (gPlusShapeImage F (source i))
  have hSourceEval (i : Nat) :
      source i = H.toGPlus family hAvoidH (hPosition k i k) := by
    have hEnum : E =
        GPlusEnumeration.enumerate H family hAvoidH :=
      GPlusEnumeration.enumerate_independent_of_witness family C H
        hAvoidC hAvoidH
    change E (H.toGOmega family hAvoidH (hPosition k i k)) =
      H.toGPlus family hAvoidH (hPosition k i k)
    rw [hEnum]
    exact H.toGOmega_eval family hAvoidH (hPosition k i k)
  have hTargetEval (i : Nat) :
      E (targetRank i) = gPlusShapeImage F (source i) :=
    E.apply_symm_apply (gPlusShapeImage F (source i))
  obtain ⟨_hInside,_hInjective,hTopStrict,hTopBinary,hTopUnary,
    hTopDiagonal⟩ :=
    infiniteNumericHL_top_induced_ordered_copy K hCarrier k
  have hSourceSize (i : Nat) :
      (source i).val.size = hPosition k i k + 1 := by
    rw [hSourceEval i]
    exact H.toGPlus_size family hAvoidH (hPosition k i k)
  have hSourceSizesStrict :
      StrictMono (fun i : Nat => (source i).val.size) := by
    intro i j hij
    rw [hSourceSize i, hSourceSize j]
    exact Nat.add_lt_add_right (hTopStrict hij) 1
  have hRankStrict : StrictMono targetRank := by
    intro i j hij
    have hLess : (source i).val.size < (source j).val.size :=
      hSourceSizesStrict hij
    have hImageLess :
        (gPlusShapeImage F (source i)).val.size <
          (gPlusShapeImage F (source j)).val.size :=
      gPlusShapeImage_size_lt_of_source_size_lt
        F (source i) (source j) hLess
    by_contra hNot
    have hBackwards : targetRank j ≤ targetRank i :=
      Nat.le_of_not_gt hNot
    have hEnumerated :=
      (GPlusEnumeration.enumerate_size_mono C family hAvoidC) hBackwards
    change (E (targetRank j)).val.size ≤
      (E (targetRank i)).val.size at hEnumerated
    rw [hTargetEval j,hTargetEval i] at hEnumerated
    omega
  refine {
    toFun := targetRank
    strictMono := hRankStrict
    inside := by intro _ _; trivial
    binary := ?_
    unary := ?_
    diagonal := ?_
  }
  · intro i j _hi _hj hij t
    have hPositionNe : hPosition k i k ≠ hPosition k j k :=
      fun h => hij (hTopStrict.injective h)
    change finiteGPlusBinary (E (targetRank i))
      (E (targetRank j)) t = K.binary i j t
    rw [hTargetEval i,hTargetEval j,
      gPlusShapeImage_preserves_binary F (source i) (source j) t]
    rw [hSourceEval i,hSourceEval j]
    exact (H.toGPlus_binary family hAvoidH hPositionNe t).trans
      (hTopBinary i j hij t)
  · intro i _hi t
    change finiteGPlusUnary (E (targetRank i)) t = K.unary i t
    rw [hTargetEval i,
      gPlusShapeImage_preserves_unary F (source i) t,
      hSourceEval i]
    exact (H.toGPlus_unary family hAvoidH (hPosition k i k) t).trans
      (hTopUnary i t)
  · intro i _hi t
    change finiteGPlusDiagonal (E (targetRank i)) t =
      K.diagonal i t
    rw [hTargetEval i,
      gPlusShapeImage_preserves_diagonal F (source i) t,
      hSourceEval i]
    exact (H.toGPlus_diagonal family hAvoidH (hPosition k i k) t).trans
      (hTopDiagonal i t)

/-- The last-stage Kpt shape Ramsey argument gives one ordered
induced embedding of the entire forbidden-free K into the FIXED
enumerated Gω, such that all its q-tuples use at most the number
of colours in the actual bounded Kpt source palette at b(q).

The conclusion quantifies over every tuple of source vertices,
including repetitions; restricting to ordered induced copies of A
immediately inherits the same bound. No tuple-dependent Ramsey
subspace or infinite approximation is chosen. -/
theorem normalizedKpt_fixedGOmega_finite_bigRamsey_transfer
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
    (χ : (Fin q → Nat) → κ) :
    ∃ (e : K.InducedEmbedding
          (finiteGPlusEnumeratedL
            (GPlusEnumeration.enumerate C family hAvoidC)))
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family
          (numericHTopUniformPaletteHeight family k q) q) ∧
      ∀ indices : Fin q → Nat,
        χ (fun i => e.toFun (indices i)) ∈ colours := by
  classical
  let E := GPlusEnumeration.enumerate C family hAvoidC
  let H := infiniteNumericHPlus K k
  let hAvoidH : ∀ bad, bad ∈ family → bad.Avoids H.L :=
    infiniteNumericHL_avoids_family family K hCarrier hAvoidK k
  let χG : (Fin q → FiniteGPlusVertex family) → κ :=
    fun t => χ (fun i => E.symm (t i))
  obtain ⟨W, colours, hCard, hEvery⟩ :=
    numericKFixedGOmegaTopTuples_uniform_colour_bound
      family C hAvoidC K hCarrier hAvoidK k hk hFamilyBound q χG
  let e : K.InducedEmbedding (finiteGPlusEnumeratedL E) :=
    numericKToFixedGOmega_after_shape
      family C hAvoidC K hCarrier hAvoidK k W.1.map
  refine ⟨e,colours,hCard,?_⟩
  intro indices
  let source : Fin q → FiniteGPlusVertex family :=
    fun i => E (H.toGOmega family hAvoidH (hPosition k (indices i) k))
  have hMem : source ∈
      numericKFixedGOmegaTopTuples
        family C hAvoidC K hCarrier hAvoidK k q := by
    exact ⟨indices,rfl⟩
  have hColour := hEvery source hMem
  change χ (fun i : Fin q =>
    E.symm (gPlusShapeImage W.1.map
      (E (H.toGOmega family hAvoidH (hPosition k (indices i) k))))) ∈
      colours at hColour
  exact hColour

end SuccessorTree.V10
