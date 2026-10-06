import SuccessorTree.FatTree.A4ReviewComplete

open SuccessorTree SuccessorTree.SMTree
open SuccessorTree.SMTree.FatTree

#check fatTreeFixedStemPigeonhole
#check fatTreeA4
#check fatTreeAbstractRamseySpace
#check fatTreeEllentuck

#print axioms fatTreeFixedStemPigeonhole
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
  fatTreeFixedStemPigeonhole H

example (H : SMTree S)
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    (O : Set ((approximationSystem H).Approx (n + 1))) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d B ∧
      ((approximationSystem H).oneStepApproximations a V ⊆ O ∨
        Disjoint ((approximationSystem H).oneStepApproximations a V) O) :=
  fatTreeA4 H a B hd O

noncomputable example (H : SMTree S) :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  fatTreeAbstractRamseySpace H

example (H : SMTree S) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  fatTreeEllentuck H
end
