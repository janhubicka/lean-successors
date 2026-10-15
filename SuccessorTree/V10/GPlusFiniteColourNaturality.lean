import SuccessorTree.V10.GPlusFiniteApproxAction
import SuccessorTree.V10.KptSimultaneousFinitePalette
import SuccessorTree.ShapeFiniteProduct
import Mathlib.Tactic

/-!
# Theorem 6.26: shape substitution acts naturally on finite G+ palettes

The finite approximant a : AM H 0 (b+1) represents a Kpt ShapeMap on
all source nodes up to level b. For each genuine bounded G+ representing
pair Q, its induced image therefore depends only on this finite
approximation, not on the chosen total representative.

Moreover ShapeFiniteProduct.shapeActK constructs a representative of
the left substitution W ∘ a which agrees with its literal total
composition on exactly this finite source segment. Combining this
checked fact with the genuine G+ ShapeMap composition law gives the
full naturality identity needed for the manuscript colouring
chi''_e(a) = chi'(Phi_{a}(e(A))).

This holds simultaneously on every actual q-tuple in the finite
bounded G+ representation palette, and hence after applying ANY
finite colouring chi' of such tuples.

No E1 assumption or new Ramsey theorem is involved in this
naturality step. It remains to use the finite Ramsey theorem to
stabilize the resulting colours and compose the ordered embeddings.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Naturality of the induced G+ image of a bounded actual
representing pair under finite Kpt ShapeMap substitution. -/
theorem gPlusShapeImage_shapeActK_naturality_pair
    (family : List (NormalizedForbidden db du dd))
    (b : Nat)
    (W : SuccessorTree.SMTree.ShapeSubspace
      (normalizedKptSMTree family) 0)
    (a : SuccessorTree.SMTree.AM
      (normalizedKptSMTree family) 0 (b+1))
    (Q : BoundedGPlusRepresentingPair family b) :
    gPlusShapeImage
      (((normalizedKptSMTree family).shapeActK 0 (b+1) W a).representative
        (normalizedKptSMTree family)).map Q.val.vertex =
      gPlusShapeImage W.1.map
        (gPlusShapeImage (a.representative (normalizedKptSMTree family)).map
          Q.val.vertex) := by
  let H := normalizedKptSMTree family
  let F : SuccessorTree.SMTree.MMap H :=
    (H.shapeActK 0 (b+1) W a).representative H
  let G : SuccessorTree.SMTree.MMap H :=
    SuccessorTree.SMTree.MMap.comp H W.1 (a.representative H)
  have hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ b → F.map x = G.map x := by
    intro x hx
    change
      (H.shapeActK 0 (b+1) W a).representative H x =
        W.1 (a.representative H x)
    exact H.shapeActK_representative_agrees 0 (b+1) W a x (by omega)
  have hFinite :=
    gPlusShapeImage_eq_of_agree_bounded_pair
      family b F.map G.map hAgree Q
  calc
    gPlusShapeImage F.map Q.val.vertex =
        gPlusShapeImage G.map Q.val.vertex := hFinite
    _ = gPlusShapeImage W.1.map
          (gPlusShapeImage (a.representative H).map Q.val.vertex) :=
      gPlusShapeImage_comp W.1.map (a.representative H).map Q.val.vertex

/-- Naturality simultaneously on every q-point tuple in the genuine
finite bounded representation palette, as required by the
colouring pullback of Theorem 6.26. -/
theorem gPlusShapeImage_shapeActK_naturality_tuple
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    (W : SuccessorTree.SMTree.ShapeSubspace
      (normalizedKptSMTree family) 0)
    (a : SuccessorTree.SMTree.AM
      (normalizedKptSMTree family) 0 (b+1))
    (e : Fin q → FiniteGPlusVertex family)
    (he : e ∈ boundedGPlusTuplePalette family b q) :
    (fun i : Fin q =>
      gPlusShapeImage
        (((normalizedKptSMTree family).shapeActK 0 (b+1) W a).representative
          (normalizedKptSMTree family)).map (e i)) =
    (fun i : Fin q =>
      gPlusShapeImage W.1.map
        (gPlusShapeImage (a.representative (normalizedKptSMTree family)).map
          (e i))) := by
  rcases he with ⟨P,hP⟩
  subst e
  funext i
  exact gPlusShapeImage_shapeActK_naturality_pair family b W a (P i)

/-- The literal manuscript colouring of finite approximations,
indexed by an ACTUAL bounded G+ tuple rather than an abstract code. -/
noncomputable def boundedGPlusApproxColour
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    {κ : Type*}
    (χ : (Fin q → FiniteGPlusVertex family) → κ)
    (e : boundedGPlusPaletteIndices family b q)
    (a : SuccessorTree.SMTree.AM
      (normalizedKptSMTree family) 0 (b+1)) : κ :=
  χ (fun i => gPlusShapeImage
    (a.representative (normalizedKptSMTree family)).map (e.val i))

/-- Substitution of a finite shape approximation agrees exactly with
substitution of its induced G+ vertex tuple before colouring.
Thus χ''_e is well-defined and compatible with the shape action,
including both positive and absent L+ atoms. -/
theorem boundedGPlusApproxColour_shapeActK
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    {κ : Type*}
    (χ : (Fin q → FiniteGPlusVertex family) → κ)
    (e : boundedGPlusPaletteIndices family b q)
    (W : SuccessorTree.SMTree.ShapeSubspace
      (normalizedKptSMTree family) 0)
    (a : SuccessorTree.SMTree.AM
      (normalizedKptSMTree family) 0 (b+1)) :
    boundedGPlusApproxColour family b q χ e
      ((normalizedKptSMTree family).shapeActK 0 (b+1) W a) =
    χ (fun i : Fin q => gPlusShapeImage W.1.map
      (gPlusShapeImage (a.representative (normalizedKptSMTree family)).map
        (e.val i))) := by
  unfold boundedGPlusApproxColour
  congr 1
  exact gPlusShapeImage_shapeActK_naturality_tuple
    family b q W a e.val e.property

end SuccessorTree.V10
