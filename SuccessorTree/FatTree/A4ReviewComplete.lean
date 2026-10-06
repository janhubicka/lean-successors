import SuccessorTree.FatTree.A4ReviewSourceFusion
import SuccessorTree.FatTree.A4Assembly

/-!
# Completed A4 and Ellentuck endpoint for fat trees

The Baumgartner-style all-trace proof supplies the geometric fixed-stem
pigeonhole theorem without an A4 hypothesis.  The independently checked A3
transfer gives Todorčević A4 for the typed fat-tree approximation system.
Metric closedness and the abstract Ellentuck theorem then give the
topological Ramsey-space conclusion.

The `*_review` names at the end are compatibility aliases for earlier
development checkpoints.  The public endpoints are the `fatTree*` names.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Geometric fixed-stem pigeonhole theorem for every finite stem and every
colour class of geometric one-block extensions. -/
theorem fatTreeFixedStemPigeonhole : FixedStemPigeonhole H := by
  intro y U hyU O
  exact review_fixedStemPigeonhole H y U hyU O

/-- Todorčević A4 for the typed fat-tree approximation space. -/
theorem fatTreeA4
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    (O : Set ((approximationSystem H).Approx (n + 1))) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d B ∧
      ((approximationSystem H).oneStepApproximations a V ⊆ O ∨
        Disjoint ((approximationSystem H).oneStepApproximations a V) O) :=
  typed_pigeonhole_of_fixedStem H (fatTreeFixedStemPigeonhole H) a B hd O

/-- A1--A4 for the fat-tree approximation space. -/
noncomputable def fatTreeAbstractRamseySpace :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  ramseySpaceOfFixedStemPigeonhole H (fatTreeFixedStemPigeonhole H)

/-- The fat-tree space is a topological Ramsey space in the literal
basic-neighbourhood formulation. -/
theorem fatTreeEllentuck :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  RamseySpace.abstractEllentuck_onBasicNeighborhoods
    (fatTreeAbstractRamseySpace H) (isMetricallyClosed H)

/-! Compatibility aliases retained for validation links from earlier
checkpoints. -/

theorem fixedStemPigeonhole_review : FixedStemPigeonhole H :=
  fatTreeFixedStemPigeonhole H

noncomputable def abstractRamseySpace_review :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  fatTreeAbstractRamseySpace H

theorem ellentuck_review :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  fatTreeEllentuck H

end SuccessorTree.SMTree.FatTree
