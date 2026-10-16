import SuccessorTree.FatTree.ShapeCorrespondence
import SuccessorTree.FatTree.A3Typed

/-!
# The canonical fat-tree projection: exact obligations

This module starts the original proof route from *fat-tree*
Ellentuck to the topological theorem on shape-preserving M-maps.

It is **not** an attempt to assert A.3(2) for M-maps. The
fat-tree reduction relation is geometric (lift inclusions),
whereas a reduction of M-maps is right composition.

The theorem `projection_surjective` is already a verified
consequence of the canonical `ofShapeMap` widening.

Two further properties are stated as propositions below, NOT
as axioms: projecting geometric reductions to algebraic
factorizations, and independence of the projected finite
prefix from the tail of a fat tree. The conditional
`projectedDepthCone_of_compatibility` proves precisely
what those properties would establish about images of
the paper's `[n,U]` neighborhoods.

Neither of the two hypotheses has been established yet.
Do not confuse `associatedMap_ofShapeMap` (surjectivity)
with the reverse lifting required by paper Lemma 4.1.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- The canonical projection from fat trees onto the original
shape-preserving monoid is surjective, by explicit widening. -/
theorem projection_surjective (H : SMTree S) :
    Function.Surjective (associatedMap H) := by
  intro F
  exact ⟨ofShapeMap H F, associatedMap_ofShapeMap H F⟩

/-- Forward compatibility needed in Lemma 4.1: geometric
fat-tree reductions must project to *right-composition*
refinements. This is an obligation, not an SMTree axiom. -/
def ProjectionRespectsReduction (H : SMTree S) : Prop :=
  ∀ (V U : FatTree H), Reduces H V U →
    RamseyReduction H (associatedMap H V) (associatedMap H U)

/-- The projected approximation through n source levels depends
only on the first n rows of the fat tree. For n = 0 this is
the unique empty approximation. This is an obligation,
not an additional SMTree axiom. -/
def ProjectionRespectsPrefixes (H : SMTree S) : Prop :=
  ∀ (V U : FatTree H) (n : Nat),
    V.initialSegment H n = U.initialSegment H n →
    ramseyApprox H n (associatedMap H V) =
      ramseyApprox H n (associatedMap H U)

/-- The exact conclusion about the fat-tree depth cone
`[n,U]`, *conditional on the two identified projection
obligations*. The first conclusion is algebraic right
factorization; the second is actual finite-prefix equality. -/
theorem projectedDepthCone_of_compatibility
    (H : SMTree S)
    (hReduction : ProjectionRespectsReduction H)
    (hPrefix : ProjectionRespectsPrefixes H)
    (U V : FatTree H) (n : Nat)
    (hVU : InDepthCone H n U V) :
    RamseyReduction H (associatedMap H V) (associatedMap H U) ∧
    ramseyApprox H n (associatedMap H V) =
      ramseyApprox H n (associatedMap H U) := by
  refine ⟨hReduction V U hVU.1, ?_⟩
  exact hPrefix V U n
    (initialSegment_eq_of_extendsStem H hVU.2)

/-- The *reverse* image of a fat basic neighborhood is
the separate relative-lifting problem; its formulation
uses an actual witness `W` realizing the stem because
`x` may be a non-prefix finite fat-tree reduction of U. -/
def ProjectionLiftsCompatibleTargets (H : SMTree S) : Prop :=
  ∀ (x : FiniteFatTree H) (U W : FatTree H),
    InNeighborhood H x U W →
    ∀ F : MMap H,
      RamseyReduction H F (associatedMap H U) →
      ramseyApprox H x.height F =
        ramseyApprox H x.height (associatedMap H W) →
      ∃ V : FatTree H,
        InNeighborhood H x U V ∧ associatedMap H V = F

end SuccessorTree.SMTree.FatTree
