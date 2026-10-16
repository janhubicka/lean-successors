import SuccessorTree.RamseySpace.Closed
import RamseySpace.AbstractEllentuck

/-!
# Exact remaining hypotheses for shape-map monoid Ellentuck

The `MMap` approximation system has a verified A.1, A.2, A.3(1),
Tychonoff closedness and fusion. This file records A.3(2) and A.4
as explicit *propositions*, not new axioms or class assumptions,
and proves that they imply the literal topological Ellentuck
conclusion of the manuscript's Theorem 1.11.

The two properties must be proved from the original M1--M3
contract before Theorem 1.11 can be claimed unconditionally.
In particular, the fat-tree theorem does not automatically
supply A.3(2) through the disputed neighborhood projection.
-/

namespace SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

/-- The exact direct M-map refinement half of Todorcevic A.3.
For `A ≤ B` and a compatible stem `a` of minimal depth `d`
in `B`, find a refinement of `B` fixed through `d`
whose `a`-neighborhood lies inside the given `a`-neighborhood
of `A`. This is NOT asserted by the present M1--M3 API. -/
def HasDirectAmalgamation (H : SMTree S) : Prop :=
  ∀ {n : Nat} (a : RamseyApprox H n) (B : MMap H) {d : Nat},
    (H.ramseyFinitization).HasDepth a B d →
    ∀ (A : MMap H),
      RamseyReduction H A B →
      ((H.ramseyApproximationSystem).neighborhood a A).Nonempty →
      ∃ A' : MMap H,
        A' ∈ (H.ramseyApproximationSystem).levelNeighborhood d B ∧
        (H.ramseyApproximationSystem).neighborhood a A' ⊆
          (H.ramseyApproximationSystem).neighborhood a A

/-- The full direct M-map one-step pigeonhole axiom A.4,
including the depth-zero empty-approximation case. -/
def HasDirectPigeonhole (H : SMTree S) : Prop :=
  ∀ {n : Nat} (a : RamseyApprox H n) (B : MMap H) {d : Nat},
    (H.ramseyFinitization).HasDepth a B d →
    ∀ O : Set (RamseyApprox H (n + 1)),
      ∃ A : MMap H,
        A ∈ (H.ramseyApproximationSystem).levelNeighborhood d B ∧
        ((H.ramseyApproximationSystem).oneStepApproximations a A ⊆ O ∨
          Disjoint
            ((H.ramseyApproximationSystem).oneStepApproximations a A) O)

/-- A.1, A.2, A.3(1), and closedness have already been proved.
Only explicit A.3(2) and A.4 witnesses are needed to construct
a full abstract Ramsey-space instance for the *actual M-maps*. -/
def directAbstractRamseySpace_of_A3A4
    (H : SMTree S)
    (hA3 : H.HasDirectAmalgamation)
    (hA4 : H.HasDirectPigeonhole) :
    RamseySpace.AbstractRamseySpace (H.ramseyApproximationSystem) where
  fin := H.ramseyFinitization
  amalgamation_nonempty := by
    intro n a B d hd A hAB
    exact H.fusionNeighborhood_nonempty a B hd hAB
  amalgamation_refine := by
    intro n a B d hd A hAB hne
    exact hA3 a B hd A hAB hne
  pigeonhole := by
    intro n a B d hd O
    exact hA4 a B hd O

/-- The manuscript's topological shape-map monoid Ellentuck
conclusion, with the only *currently unverified* conditions
stated explicitly.

Once A.3(2) and A.4 are discharged, this is the literal
Chapter 5 (basic-neighborhood) form, not merely an Ellentuck
theorem on the separate fat-tree space. -/
theorem directMonoidEllentuck_of_A3A4
    (H : SMTree S)
    (hA3 : H.HasDirectAmalgamation)
    (hA4 : H.HasDirectPigeonhole) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := H.ramseyApproximationSystem) :=
  RamseySpace.abstractEllentuck_textbook
    (H.directAbstractRamseySpace_of_A3A4 hA3 hA4)
    (H.ramseyApproximation_isTychonoffClosed)

end SuccessorTree.SMTree
