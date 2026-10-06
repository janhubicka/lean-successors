import SuccessorTree.FatTree.A4ReviewComplete

open SuccessorTree SuccessorTree.SMTree
open SuccessorTree.SMTree.FatTree

/- Referee B: stress the cases that were historically easy to miss:
moving roots, roots with no source letter, arbitrary last-block
factorisation, and the unconditional final statement. -/

section
universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

example (H : SMTree S)
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (E : OneLevelLetter H y.terminalCut)
    (O : Set (AM H y.terminalCut 1)) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ((∀ g, OneBlockOccurs H y V g → g ∈ O) ∨
       (∀ g, OneBlockOccurs H y V g → g ∉ O)) :=
  review_fixedStemPigeonhole_of_sourceLetter H y U hyU E O

example (H : SMTree S) (c : Nat)
    (hno : ¬ Nonempty (OneLevelLetter H c))
    (g k : AM H c 1) : g = k :=
  review_rows_eq_of_no_sourceLetter H c hno g k

example (H : SMTree S)
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (E : OneLevelLetter H y.terminalCut)
    (m : Nat) (hym : y.height ≤ m)
    (g : AM H y.terminalCut 1)
    (hg : StemAt H (FiniteFatTree.appendRow H y g) U (m + 1)) :
    ∃ p : FiniteFatTree.ExactTrace H
        (U.initialSegment H m) y.height hym,
      HEq g
        (H.composeAcross
          (exactTraceToAMExact H (U.initialSegment H m)
            y.height hym p)
          (U.row m)) :=
  exists_lastBlock_exactTrace_of_sourceLetter H y U hyU E m hym g hg

example (H : SMTree S) : FixedStemPigeonhole H :=
  fatTreeFixedStemPigeonhole H
end

#print axioms review_fixedStemPigeonhole_of_sourceLetter
#print axioms review_rows_eq_of_no_sourceLetter
#print axioms exists_lastBlock_exactTrace_of_sourceLetter
#print axioms review_goodPair_at_prefix_of_sourceLetter
#print axioms fatTreeFixedStemPigeonhole
#print axioms fatTreeA4
