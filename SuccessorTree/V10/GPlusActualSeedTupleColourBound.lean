import SuccessorTree.V10.GPlusFiniteBigRamseyTransfer
import SuccessorTree.V10.GPlusAlgorithmFinitePalette
import SuccessorTree.ShapeFiniteProduct
import SuccessorTree.V10.KptE1EnvelopeIntegration

/-!
# Actual Algorithm 5.4 seed tuples satisfy finite approximation palette coverage

The bounded-palette output of the *actual* Kpt AlgorithmRun was previously
expressed using the full output MMap R.F 0. The final colouring theorem needs
the exact \`FiniteGPlusPaletteCovers\` predicate: the same target tuple must
be the image of a genuinely finite AM approximation. These are equivalent
on a bounded source palette, because the canonical AM of R.F 0 agrees with
R.F 0 on every source Kpt node at or below the palette bound.

This is the finite-approximation bridge, not a new Ramsey axiom. The hypotheses are the seed-height/top-original conditions, together with
representation of every target tuple's coordinates by
actual strict Kpt pairs whose two endpoints lie in the chosen seed set.
The last requirement is *not* asserted for all copies of A in G omega.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- The source palette supplied by a genuine AlgorithmRun represents
the required target seed tuples via ONE finite AM approximation of the
actual output map, not merely via an unbounded total ShapeMap. -/
theorem numericKptAlgorithmRun_seed_tuples_finiteApprox_cover
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family)) (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hBound : X ⊆ SuccessorTree.SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family) ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (q : Nat)
    (targets : Set (Fin q → FiniteGPlusVertex family))
    (hPairs : ∀ t, t ∈ targets → ∀ i : Fin q,
      ∃ P : GPlusRepresentingPair family,
        P.vertex = t i ∧ P.lower ∈ X ∧ P.upper ∈ X) :
    FiniteGPlusPaletteCovers family R.selectedLevels.card q targets := by
  classical
  let H := normalizedKptSMTree family
  let F : SuccessorTree.SMTree.MMap H := R.F 0
  have hFix : F.FixesBelow H 0 := by
    intro x hx
    omega
  let a : SuccessorTree.SMTree.AM H 0 (R.selectedLevels.card + 1) :=
    F.toAM H 0 (R.selectedLevels.card + 1) hFix
  have hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ R.selectedLevels.card →
        (a.representative H).map x = F.map x := by
    intro x hx
    exact SuccessorTree.SMTree.MMap.toAM_representative_agrees
      H F 0 (R.selectedLevels.card + 1) hFix x (by omega)
  intro t ht
  obtain ⟨sources, hPalette, hImage⟩ :=
    numericKptAlgorithmRun_GPlus_seed_tuple_from_finite_palette
      family X ell R
      (normalizedKpt_oneLevelPullback_for_envelopes family)
      hBound hTop q t (hPairs t ht)
  have hTuple :=
    gPlusShapeImage_eq_of_agree_bounded_tuple
      family R.selectedLevels.card q
      (a.representative H).map F.map hAgree sources hPalette
  refine ⟨⟨sources, hPalette⟩, a, ?_⟩
  intro i
  exact (congrFun hTuple i).trans (hImage i)

/-- Compose the actual AlgorithmRun source-palette geometry with the
finite product-colouring Ramsey argument. The colour bound is the
cardinality of the *actual* finite palette at the number of selected
levels of this run, not an arbitrary assumed colour bound. -/
theorem numericKptAlgorithmRun_seed_tuples_finiteColour_bound
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (X : Set (AdmissibleKptNode family)) (ell : Nat)
    (R : SuccessorTree.SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X ell)
    (hBound : X ⊆ SuccessorTree.SMTree.Envelope.levelLe
      (T := AdmissibleKptNode family) ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell)
    (q : Nat)
    (targets : Set (Fin q → FiniteGPlusVertex family))
    (hPairs : ∀ t, t ∈ targets → ∀ i : Fin q,
      ∃ P : GPlusRepresentingPair family,
        P.vertex = t i ∧ P.lower ∈ X ∧ P.upper ∈ X)
    (χ : (Fin q → FiniteGPlusVertex family) → κ) :
    ∃ (W : SuccessorTree.SMTree.ShapeSubspace
          (normalizedKptSMTree family) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family R.selectedLevels.card q) ∧
      ∀ t, t ∈ targets →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  exact normalizedKpt_GPlus_finite_colour_bound_of_cover
    family R.selectedLevels.card q targets χ
    (numericKptAlgorithmRun_seed_tuples_finiteApprox_cover
      family X ell R hBound hTop q targets hPairs)

end SuccessorTree.V10
