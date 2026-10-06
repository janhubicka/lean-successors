import SuccessorTree.RamseySpace.Ellentuck

open SuccessorTree
open SuccessorTree.SMTree

#check shapeIsMetricallyClosed
#check shapePigeonhole_zero
#check shapePigeonhole
#check ShapeEllentuckAmalgamation
#check shapeAbstractRamseySpace
#check shapeEllentuck
#check shapeEllentuck_baire
#check shapeEllentuck_meagre

#print axioms shapeIsMetricallyClosed
#print axioms shapePigeonhole_zero
#print axioms shapePigeonhole
#print axioms shapeAbstractRamseySpace
#print axioms shapeEllentuck
#print axioms shapeEllentuck_baire
#print axioms shapeEllentuck_meagre

/- Interface guards: A4 and closedness do not take EA; the final
topological endpoint takes exactly the optional A3(2) hypothesis. -/
section InterfaceGuard
universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

example (H : SMTree S) :
    (ramseyApproximationSystem H).IsMetricallyClosed :=
  shapeIsMetricallyClosed H

example (H : SMTree S)
    {n : Nat} (a : RamseyApprox H n) (B : MMap H) {d : Nat}
    (hd : (ramseyFinitization H).HasDepth a B d)
    (O : Set (RamseyApprox H (n + 1))) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
        Disjoint ((ramseyApproximationSystem H).oneStepApproximations a A) O) :=
  shapePigeonhole H a B hd O

example (H : SMTree S) (hEA : ShapeEllentuckAmalgamation H) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) :=
  shapeEllentuck H hEA
end InterfaceGuard
