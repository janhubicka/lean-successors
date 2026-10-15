import SuccessorTree.V10.GPlusPaletteRamseyStabilization
import Mathlib.Tactic

/-!
# Theorem 6.26: finite big Ramsey colour bound from actual bounded palette coverage

The normalized Kpt tree already satisfies the complete successor Ramsey
theorem. The genuine G+ action is induced, and the actual bounded Kpt
representation palette is finite. Its finite approximation action is
well defined, natural under substitution, and the finite product-colouring
Ramsey theorem stabilizes ALL palette indices simultaneously.

The only geometric input needed to deduce a finite colour bound on a
particular family of q-tuples is therefore the literal coverage property:
each target tuple has an actual bounded palette source e and a genuine
finite Kpt approximation a such that target = Phi_a(e).

This file proves that implication with an EXPLICIT upper bound:
the number of colours on the transformed family is at most the
cardinality of the finite bounded representation palette. It does not
assume an abstract Ramsey theorem or introduce an E1 axiom.

The final K universal-structure application still has to prove this
coverage for every required A-copy via the concrete numerical H+
envelope construction and its uniform height bound, and supply the
ordered K→Gω→K embedding. The Section 5 E1 dependency must be
proved for the genuine Kpt tree or bypassed with another envelope
argument. This theorem deliberately exposes that boundary.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat} {κ : Type*}
variable [Fintype κ]

/-- The exact bounded-palette coverage hypothesis for a specified
family of tuples in actual G+. Every target factors through a
genuine finite source palette tuple and an AM finite Kpt map,
not through an arbitrary countable representation. -/
def FiniteGPlusPaletteCovers
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    (targets : Set (Fin q → FiniteGPlusVertex family)) : Prop :=
  ∀ t, t ∈ targets →
    ∃ (e : boundedGPlusPaletteIndices family b q)
      (a : SuccessorTree.SMTree.AM
        (normalizedKptSMTree family) 0 (b+1)),
        ∀ i : Fin q,
          gPlusShapeImage
            (a.representative (normalizedKptSMTree family)).map
            (e.val i) = t i

/-- The exact final Ramsey counting implication: if all desired
tuples are covered by the true bounded source palette, a single
genuine Kpt ShapeSubspace reduces their colouring to at most as
many values as the palette has elements. -/
theorem normalizedKpt_GPlus_finite_colour_bound_of_cover
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    (targets : Set (Fin q → FiniteGPlusVertex family))
    (χ : (Fin q → FiniteGPlusVertex family) → κ)
    (hCover : FiniteGPlusPaletteCovers family b q targets) :
    ∃ (W : SuccessorTree.SMTree.ShapeSubspace
          (normalizedKptSMTree family) 0)
      (colours : Finset κ),
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family b q) ∧
      ∀ t, t ∈ targets →
        χ (fun i : Fin q => gPlusShapeImage W.1.map (t i)) ∈ colours := by
  classical
  let H := normalizedKptSMTree family
  let a0 : SuccessorTree.SMTree.AM H 0 (b+1) :=
    (SuccessorTree.SMTree.MMap.id H).toAM H 0 (b+1)
      (SuccessorTree.SMTree.MMap.id_fixesBelow H 0)
  obtain ⟨W,hW⟩ :=
    normalizedKpt_GPlus_palette_colour_stabilization family b q χ
  let colours : Finset κ :=
    Finset.univ.image (fun e : boundedGPlusPaletteIndices family b q =>
      χ (fun i : Fin q =>
        gPlusShapeImage W.1.map
          (gPlusShapeImage (a0.representative H).map (e.val i))))
  have hCard :
      colours.card ≤ Fintype.card
        (boundedGPlusPaletteIndices family b q) := by
    calc
      colours.card ≤ (Finset.univ :
        Finset (boundedGPlusPaletteIndices family b q)).card :=
          Finset.card_image_le
      _ = Fintype.card (boundedGPlusPaletteIndices family b q) :=
          Finset.card_univ
  refine ⟨W,colours,hCard,?_⟩
  intro t ht
  obtain ⟨e,a,hFact⟩ := hCover t ht
  have hEq :
      (fun i : Fin q => gPlusShapeImage W.1.map (t i)) =
      (fun i : Fin q => gPlusShapeImage W.1.map
        (gPlusShapeImage (a.representative H).map (e.val i))) := by
    funext i
    rw [hFact i]
  rw [hEq]
  apply Finset.mem_image.mpr
  refine ⟨e,Finset.mem_univ e,?_⟩
  change χ (fun i : Fin q =>
    gPlusShapeImage W.1.map
      (gPlusShapeImage (a0.representative H).map (e.val i))) =
    χ (fun i : Fin q =>
      gPlusShapeImage W.1.map
        (gPlusShapeImage (a.representative H).map (e.val i)))
  exact (hW e a a0).symm

end SuccessorTree.V10
