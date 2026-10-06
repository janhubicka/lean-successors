import SuccessorTree.FatTree.A4ReviewSourceFusion
import SuccessorTree.FatTree.A4Assembly

/-!
# Completed alternative A4 / Ellentuck endpoint for fat trees

The Baumgartner-style review proof supplies the literal-stem pigeonhole
statement without an A4 hypothesis.  The previously checked A3 transfer then
produces Todorcevic A4, and metric closedness plus the abstract Ellentuck
theorem gives the topological Ramsey-space conclusion.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- The alternative proof discharges the geometric fixed-stem obligation. -/
theorem fixedStemPigeonhole_review : FixedStemPigeonhole H := by
  intro y U hyU O
  exact review_fixedStemPigeonhole H y U hyU O

/-- A1--A4 for the fat-tree approximation space, obtained from the review
proof of A4 and the independently checked A1--A3 development. -/
noncomputable def abstractRamseySpace_review :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  ramseySpaceOfFixedStemPigeonhole H (fixedStemPigeonhole_review H)

/-- The fat-tree space is a topological Ramsey space in the literal
basic-neighbourhood formulation of the abstract Ellentuck theorem. -/
theorem ellentuck_review :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  ellentuck_of_fixedStemPigeonhole H (fixedStemPigeonhole_review H)

/-- Final public geometric fixed-stem pigeonhole theorem.  The `review`
suffix on the construction lemmas is historical; no additional hypothesis
remains here. -/
theorem fatTreeFixedStemPigeonhole : FixedStemPigeonhole H :=
  fixedStemPigeonhole_review H

/-- Final public Todorčević A4 theorem for the typed fat-tree approximation
space. -/
theorem fatTreeA4
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    (O : Set ((approximationSystem H).Approx (n + 1))) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d B ∧
      ((approximationSystem H).oneStepApproximations a V ⊆ O ∨
        Disjoint ((approximationSystem H).oneStepApproximations a V) O) :=
  typed_pigeonhole_of_fixedStem H (fatTreeFixedStemPigeonhole H) a B hd O

/-- Final public A1--A4 structure for fat trees. -/
noncomputable def fatTreeAbstractRamseySpace :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  ramseySpaceOfFixedStemPigeonhole H (fatTreeFixedStemPigeonhole H)

/-- Final public Ellentuck endpoint for the fat-tree space. -/
theorem fatTreeEllentuck :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  RamseySpace.abstractEllentuck_onBasicNeighborhoods
    (fatTreeAbstractRamseySpace H) (isMetricallyClosed H)

end SuccessorTree.SMTree.FatTree
