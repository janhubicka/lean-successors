import SuccessorTree.FatTree.ShapeTransfer

open SuccessorTree
open SuccessorTree.SMTree

#check shapeIsMetricallyClosed
#check shapePigeonhole_zero
#check shapePigeonhole
#check ShapeEllentuckAmalgamation
#check shapeAbstractRamseySpace
#check shapeEllentuck
#check ShapeNormalizedEA
#check shapeNormalizedEA_iff
#check shapeEllentuck_of_normalizedEA
#check FatTree.canonicalMap
#check FatTree.exactCanonicalApprox
#check FatShapeEllentuckTransfer
#check FatShapeEllentuckTransfer.shapeAmalgamation
#check FatShapeEllentuckTransfer.normalizedEA
#check FatShapeEllentuckTransfer.shapeEllentuck_from_fatTree

#print axioms shapeIsMetricallyClosed
#print axioms shapePigeonhole_zero
#print axioms shapePigeonhole
#print axioms shapeAbstractRamseySpace
#print axioms shapeEllentuck
#print axioms shapeNormalizedEA_iff
#print axioms shapeEllentuck_of_normalizedEA
#print axioms FatTree.canonicalMap
#print axioms FatTree.exactCanonicalApprox_exactApprox
#print axioms FatShapeEllentuckTransfer.levelNeighborhood_forward
#print axioms FatShapeEllentuckTransfer.shapeAmalgamation
#print axioms FatShapeEllentuckTransfer.normalizedEA
#print axioms FatShapeEllentuckTransfer.shapeEllentuck_from_fatTree

/- Interface guards: A4 and closedness do not take EA; the final
topological endpoint takes exactly A3(2), while the fat-tree transfer
discharges that hypothesis from exact canonical neighborhood geometry. -/
section InterfaceGuard
universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

example (H : SMTree S) :
    (ramseyApproximationSystem H).IsMetricallyClosed :=
  shapeIsMetricallyClosed H

example (H : SMTree S)
    {n : Nat} (a : (ramseyApproximationSystem H).Approx n)
    (B : MMap H) {d : Nat}
    (hd : (ramseyFinitization H).HasDepth a B d)
    (O : Set ((ramseyApproximationSystem H).Approx (n + 1))) :
    ∃ A : MMap H,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B ∧
      ((ramseyApproximationSystem H).oneStepApproximations a A ⊆ O ∨
        Disjoint ((ramseyApproximationSystem H).oneStepApproximations a A) O) :=
  shapePigeonhole H a B hd O

example (H : SMTree S) (hEA : ShapeEllentuckAmalgamation H) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) :=
  shapeEllentuck H hEA

example (H : SMTree S) (Q : FatShapeEllentuckTransfer H) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) :=
  Q.shapeEllentuck_from_fatTree H
end InterfaceGuard
