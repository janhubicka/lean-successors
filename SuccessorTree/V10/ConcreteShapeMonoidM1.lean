import SuccessorTree.V10.AdmissibleSigmaSTree
import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# The concrete Kpt shape-morphism monoid: M1

The paper's monoid M for Kpt is the family of ALL shape-preserving
maps with respect to the precise admissible-Sigma successor operation.

The abstract ShapeMap implementation already proves that the
identity, composite and pointwise frozen fusion limit remain
shape-preserving. Taking all such maps means M1 is a genuine
specialization of those results; it does not require any new
assumption on forbidden structures or the successor graph.

This module gives an exact, separate certificate for M1 in the
normalized Kpt model. It does not assert M2 (one-level gap
factorization) or M3 (boring duplication): those depend on the
forbidden-age extension argument and are still open.
-/

namespace SuccessorTree.V10

/-- The entire class of shape-preserving self-maps of the verified
admissible Kpt S-tree, exactly as in the manuscript's monoid M. -/
def admissibleKptAllShapeMaps
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    Set (SuccessorTree.ShapeMap (admissibleKptSTree family)) :=
  Set.univ

/-- M1: identity belongs to all Kpt shape-preserving maps. -/
theorem admissibleKptM1_identity
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    SuccessorTree.ShapeMap.id (admissibleKptSTree family) ∈
      admissibleKptAllShapeMaps family := by
  exact Set.mem_univ _

/-- M1: composition of shape-preserving Kpt maps is again
shape-preserving. The composition is the abstract checked
shape-map composition, not arbitrary endomorphism composition. -/
theorem admissibleKptM1_composition
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F G : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ admissibleKptAllShapeMaps family)
    (hG : G ∈ admissibleKptAllShapeMaps family) :
    F.comp G ∈ admissibleKptAllShapeMaps family := by
  exact Set.mem_univ _

/-- M1: the frozen pointwise fusion limit stays in the actual
Kpt shape-preserving map monoid, with the standard fusion-stability
hypothesis from the paper. -/
theorem admissibleKptM1_fusion
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : Nat → SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hMembers : ∀ i, F i ∈ admissibleKptAllShapeMaps family)
    (hStable : SuccessorTree.ShapeMap.FusionStable F) :
    SuccessorTree.ShapeMap.fusionLimit F hStable ∈
      admissibleKptAllShapeMaps family := by
  exact Set.mem_univ _

/-- M1 is established as all three closure laws, without
equating this to the stronger SMTree axioms M2/M3. -/
theorem admissibleKptM1
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    (SuccessorTree.ShapeMap.id (admissibleKptSTree family) ∈
      admissibleKptAllShapeMaps family) ∧
    (∀ F G : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F ∈ admissibleKptAllShapeMaps family →
      G ∈ admissibleKptAllShapeMaps family →
      F.comp G ∈ admissibleKptAllShapeMaps family) ∧
    (∀ (F : Nat → SuccessorTree.ShapeMap
        (admissibleKptSTree family))
        (hStable : SuccessorTree.ShapeMap.FusionStable F),
      (∀ i, F i ∈ admissibleKptAllShapeMaps family) →
      SuccessorTree.ShapeMap.fusionLimit F hStable ∈
        admissibleKptAllShapeMaps family) := by
  refine ⟨admissibleKptM1_identity family, ?_, ?_⟩
  · intro F G hF hG
    exact admissibleKptM1_composition family F G hF hG
  · intro F hStable hMembers
    exact admissibleKptM1_fusion family F hMembers hStable

end SuccessorTree.V10
