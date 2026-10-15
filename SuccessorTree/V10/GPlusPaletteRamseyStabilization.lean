import SuccessorTree.V10.GPlusFiniteColourNaturality
import SuccessorTree.V10.KptSimultaneousFinitePalette
import Mathlib.Tactic

/-!
# Theorem 6.26: one Kpt subspace stabilizes all bounded G+ palette colours

The finite bounded genuine G+ representation palette is a concrete
Fintype, not a new finiteness axiom. Every palette tuple e induces
a finite approximation colouring χ''_e on AM H 0 (b+1).

The verified Kpt finite-shape Ramsey theorem makes all these
colourings homogeneous simultaneously, by applying Ramsey once to
their finite product. The checked naturality law then turns the
homogeneity statement into the literal manuscript assertion that
χ(Phi_W(Phi_a(e))) does not depend on the chosen finite
approximation a, for EVERY palette tuple e.

This is an unconditional finite-colour stabilization statement for
the genuine normalized Kpt (S,M)-tree, independent of the separate
geometric envelope/E1 hypotheses. The remaining final transfer
must show that each relevant copy of A admits some bounded
source representative e under the chosen envelope and that the
final copy K is embedded into the target universal structure.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat} {κ : Type*}
variable [Fintype κ]

/-- Exactly the finite-colouring stabilization claimed in the final
proof, simultaneously for ALL real bounded G+ palette tuples.
The Kpt ShapeSubspace W is obtained from the already verified
successor Ramsey theorem; the conclusion concerns literal
G+ images via gPlusShapeImage (not an abstract action interface). -/
theorem normalizedKpt_GPlus_palette_colour_stabilization
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    (χ : (Fin q → FiniteGPlusVertex family) → κ) :
    ∃ W : SuccessorTree.SMTree.ShapeSubspace
      (normalizedKptSMTree family) 0,
      ∀ (e : boundedGPlusPaletteIndices family b q)
        (a c : SuccessorTree.SMTree.AM
          (normalizedKptSMTree family) 0 (b+1)),
        χ (fun i : Fin q =>
          gPlusShapeImage W.1.map
            (gPlusShapeImage
              (a.representative (normalizedKptSMTree family)).map
              (e.val i))) =
        χ (fun i : Fin q =>
          gPlusShapeImage W.1.map
            (gPlusShapeImage
              (c.representative (normalizedKptSMTree family)).map
              (e.val i))) := by
  let col :
      boundedGPlusPaletteIndices family b q →
        SuccessorTree.SMTree.AM
          (normalizedKptSMTree family) 0 (b+1) → κ :=
    fun e a => boundedGPlusApproxColour family b q χ e a
  obtain ⟨W,hW⟩ :=
    normalizedKpt_shapeRamsey_boundedGPlusPalette
      family b q 0 (b+1) col
  refine ⟨W, ?_⟩
  intro e a c
  calc
    χ (fun i : Fin q => gPlusShapeImage W.1.map
        (gPlusShapeImage
          (a.representative (normalizedKptSMTree family)).map
          (e.val i))) =
      col e ((normalizedKptSMTree family).shapeActK 0 (b+1) W a) :=
        (boundedGPlusApproxColour_shapeActK
          family b q χ e W a).symm
    _ = col e ((normalizedKptSMTree family).shapeActK 0 (b+1) W c) :=
      hW e a c
    _ = χ (fun i : Fin q => gPlusShapeImage W.1.map
          (gPlusShapeImage
            (c.representative (normalizedKptSMTree family)).map
            (e.val i))) :=
      boundedGPlusApproxColour_shapeActK family b q χ e W c

end SuccessorTree.V10
