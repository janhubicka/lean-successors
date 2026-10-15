import SuccessorTree.V10.GPlusComparableAtoms
import SuccessorTree.V10.GPlusShapeImageSingletonAtoms
import Mathlib.Tactic

/-!
# Observation 6.42: the genuine induced L+ action on all of G+

The canonical image of a valid G+ vertex under a genuine Kpt ShapeMap
is already constructed, and independently checked:
- genuine finite admissibility and full representative-pair
  well-definedness;
- equality reflection and injectivity on finite codes;
- identity and composition;
- full finite-code prefix preservation and reflection;
- both directed off-diagonal binary orientations and auxiliary E atoms
  on comparable and incomparable pairs;
- unary predicates and binary diagonal atoms on individual vertices.

This file collects those REAL proved statements into one explicit
induced L+ embedding certificate. There is no assumption that a G+
action exists, and no new abstract 'well-behaved action' axiom.

G+ itself is not globally enumerated, so we intentionally do NOT
claim global preservation of an arbitrary tie-breaking order on the
size-layers of its enumerated copy G^omega. The final ordered K copy
uses strictly increasing code sizes along the constructed H+ chain.

The separate finite-approximation colouring and envelope coverage
steps are still needed for Theorem 6.26.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- The complete induced structural action of EVERY genuine admissible
Kpt ShapeMap on the actual finite G+ vertices. It is injective,
reflects proper prefixes and preserves each L+ Boolean atomic table
in both directions, including all absent facts and incomparable pairs.

This is the full relational half of manuscript Observation 6.42. -/
theorem gPlusShapeImage_induced_LPlus
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    Function.Injective (gPlusShapeImage F) ∧
    (∀ A B : FiniteGPlusVertex family, ∀ t : Fin db,
      finiteGPlusBinary (gPlusShapeImage F A) (gPlusShapeImage F B) t =
        finiteGPlusBinary A B t) ∧
    (∀ A : FiniteGPlusVertex family, ∀ t : Fin du,
      finiteGPlusUnary (gPlusShapeImage F A) t =
        finiteGPlusUnary A t) ∧
    (∀ A : FiniteGPlusVertex family, ∀ t : Fin dd,
      finiteGPlusDiagonal (gPlusShapeImage F A) t =
        finiteGPlusDiagonal A t) ∧
    (∀ A B : FiniteGPlusVertex family,
      finiteGPlusE (gPlusShapeImage F A) (gPlusShapeImage F B) =
        finiteGPlusE A B) ∧
    (∀ A B : FiniteGPlusVertex family,
      (gPlusShapeImage F A).IsProperPrefix (gPlusShapeImage F B) ↔
        A.IsProperPrefix B) := by
  refine ⟨gPlusShapeImage_injective F, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B t
    exact gPlusShapeImage_preserves_binary F A B t
  · intro A t
    exact gPlusShapeImage_preserves_unary F A t
  · intro A t
    exact gPlusShapeImage_preserves_diagonal F A t
  · intro A B
    exact gPlusShapeImage_preserves_E F A B
  · intro A B
    exact gPlusShapeImage_properPrefix_iff F A B

end SuccessorTree.V10
