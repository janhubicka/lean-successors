import SuccessorTree.FatTree.A4ReviewSourceFusion
import SuccessorTree.FatTree.A4Assembly

/-!
# Completed A4 and Ellentuck endpoint for fat trees

The Baumgartner-style all-trace proof supplies the geometric fixed-stem
pigeonhole theorem without an A4 hypothesis.  The independently checked A3
transfer gives Todorčević A4 for the typed fat-tree approximation system.
Metric closedness and the abstract Ellentuck theorem then give the
topological Ramsey-space conclusion.

The public `fatTree*` endpoints below are unconditional: they carry no
hidden A4, positivity, root-cut, saturation, or good-pair premise.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

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
  ellentuck_of_fixedStemPigeonhole H (fatTreeFixedStemPigeonhole H)

end SuccessorTree.SMTree.FatTree
