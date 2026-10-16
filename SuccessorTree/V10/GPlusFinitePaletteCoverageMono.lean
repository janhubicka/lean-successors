import SuccessorTree.V10.GPlusHTopUniformPalette
import SuccessorTree.V10.GPlusFiniteApproxAction

/-!
# Uniformly enlarge a genuine finite G+ representation palette

The bounded palette coverage predicate uses both a tuple of genuine
Kpt representing pairs of upper level at most b and a genuine finite
Kpt approximation of height b+1. It is *not* enough to include only
the first tuple in a larger palette: the approximation must be
coherently enlarged as well.

Any finite approximation has an actual total representative in the
root-preserving Kpt monoid. Taking a new finite approximation of
this SAME representative through B+1 agrees on all earlier nodes.
Because every representing pair has upper level at most b≤B,
its G+ image is unchanged. This proves an exact monotonicity
statement for the full FiniteGPlusPaletteCovers predicate.

The result is useful for the universal Section 6 proof: different
copies of a fixed A may have different numerical envelopes, but
once their heights are uniformly bounded they all factor through
one and the same finite palette at the upper bound B.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- An actual bounded G+ tuple factorization at height b can
be re-expressed at any larger height B. The enlarged Kpt finite
approximation is obtained from the original approximation's
genuine total representative, and the entire tuple action agrees
exactly, including all absent directed L and E atoms. -/
theorem finiteGPlusPaletteCovers_mono
    (family : List (NormalizedForbidden db du dd))
    {b B q : Nat} (h : b ≤ B)
    (targets : Set (Fin q → FiniteGPlusVertex family))
    (hCover : FiniteGPlusPaletteCovers family b q targets) :
    FiniteGPlusPaletteCovers family B q targets := by
  classical
  let H := normalizedKptSMTree family
  intro t ht
  obtain ⟨e, a, hFactor⟩ := hCover t ht
  let F : SuccessorTree.SMTree.MMap H := a.representative H
  have hFix : F.FixesBelow H 0 := by
    intro x hx
    omega
  let aBig : SuccessorTree.SMTree.AM H 0 (B+1) :=
    F.toAM H 0 (B+1) hFix
  let eBig : boundedGPlusPaletteIndices family B q :=
    ⟨e.val, boundedGPlusTuplePalette_mono family h e.property⟩
  have hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ b →
        (aBig.representative H).map x = F.map x := by
    intro x hx
    exact SuccessorTree.SMTree.MMap.toAM_representative_agrees
      H F 0 (B+1) hFix x (by omega)
  have hTuple :
      (fun i : Fin q =>
        gPlusShapeImage (aBig.representative H).map (e.val i)) =
      (fun i : Fin q => gPlusShapeImage F.map (e.val i)) :=
    gPlusShapeImage_eq_of_agree_bounded_tuple
      family b q (aBig.representative H).map F.map
      hAgree e.val e.property
  refine ⟨eBig, aBig, ?_⟩
  intro i
  exact (congrFun hTuple i).trans (hFactor i)

end SuccessorTree.V10
