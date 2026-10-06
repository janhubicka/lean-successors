import SuccessorTree.FatTree.A4ReviewComplete

open SuccessorTree SuccessorTree.SMTree
open SuccessorTree.SMTree.FatTree

#check fatTreeA4
#check fatTreeAbstractRamseySpace
#check fatTreeEllentuck

#print axioms fatTreeA4
#print axioms fatTreeAbstractRamseySpace
#print axioms fatTreeEllentuck

/- Referee A: the public endpoints must be unconditional. -/
section
universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

example (H : SMTree S) : FixedStemPigeonhole H :=
  fatTreeA4 H

example (H : SMTree S) :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  fatTreeAbstractRamseySpace H

example (H : SMTree S) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  fatTreeEllentuck H
end
