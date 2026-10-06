import SuccessorTree.RamseySpace.Closed
import SuccessorTree.RamseySpace.Pigeonhole
import RamseySpace.AbstractEllentuck

/-!
# Optional Ellentuck theorem for shape-preserving maps

The unrestricted embedding-space Ellentuck statement is false.  The missing
hypothesis is the continuation amalgamation called (EA) in the manuscript.
At the abstract Ramsey-space level this is exactly Todorčević A3(2).

A1 and A2 are already encoded by `ramseyApproximationSystem` and
`ramseyFinitization`.  A3(1) is the finite-factorization theorem
`fusionNeighborhood_nonempty`.  A4 is `shapePigeonhole`, obtained from
the one-moving-level shape Ramsey theorem and does not use EA.  Metric
closedness follows from M1.

This file first exposes the exact A3(2) interface.  A subsequent concrete
file proves that the manuscript's normalized (EA) condition implies it.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Optional Ellentuck amalgamation in its invariant Ramsey-space form.

Whenever `A ∈ [a,B]` and `d = depth_B(a)`, one can refine inside
`[d,B]` so that every continuation above `a` is already a continuation
inside `A`.  This is Todorčević A3(2), and is the only extra hypothesis
needed for the full composition-Ellentuck theorem. -/
def ShapeEllentuckAmalgamation (H : SMTree S) : Prop :=
  ∀ {n : Nat} (a : RamseyApprox H n) (B : MMap H) {d : Nat},
    (ramseyFinitization H).HasDepth a B d →
    ∀ {A : MMap H},
      A ∈ (ramseyApproximationSystem H).neighborhood a B →
      ∃ A' : MMap H,
        A' ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
        (ramseyApproximationSystem H).neighborhood a A' ⊆
          (ramseyApproximationSystem H).neighborhood a A

/-- Under EA the shape-preserving map space satisfies A1--A4. -/
noncomputable def shapeAbstractRamseySpace
    (H : SMTree S)
    (hEA : ShapeEllentuckAmalgamation H) :
    RamseySpace.AbstractRamseySpace (ramseyApproximationSystem H) :=
  RamseySpace.AbstractRamseySpace.ofStandardAxioms
    (ramseyFinitization H)
    (fusionNeighborhood_nonempty H)
    (by
      intro n a B d hd A hA
      exact hEA a B hd hA)
    (shapePigeonhole H)

/-- Optional shape-preserving Ellentuck theorem in the literal
basic-neighborhood formulation.

This is the manuscript's full embedding-space conclusion under EA. -/
theorem shapeEllentuck
    (H : SMTree S)
    (hEA : ShapeEllentuckAmalgamation H) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) :=
  RamseySpace.abstractEllentuck_onBasicNeighborhoods
    (shapeAbstractRamseySpace H hEA)
    (shapeIsMetricallyClosed H)

/-- Baire-property half of the optional shape Ellentuck theorem. -/
theorem shapeEllentuck_baire
    (H : SMTree S)
    (hEA : ShapeEllentuckAmalgamation H)
    {X : Set (MMap H)}
    (hX :
      @BaireMeasurableSet (MMap H)
        (ramseyApproximationSystem H).ellentuckTopology X) :
    RamseySpace.IsRamseyOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) X :=
  (shapeEllentuck H hEA).1 X hX

/-- Meagre/Ramsey-null half of the optional shape Ellentuck theorem. -/
theorem shapeEllentuck_meagre
    (H : SMTree S)
    (hEA : ShapeEllentuckAmalgamation H)
    {X : Set (MMap H)}
    (hX :
      @IsMeagre (MMap H)
        (ramseyApproximationSystem H).ellentuckTopology X) :
    RamseySpace.IsRamseyNullOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) X :=
  (shapeEllentuck H hEA).2 X hX

end SMTree
end SuccessorTree
