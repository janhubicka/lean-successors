import SuccessorTree.FatTree.A4TypedBridge
import SuccessorTree.FatTree.Closed
import RamseySpace.AbstractEllentuck

/-!
# From the geometric fixed-stem pigeonhole statement to Ellentuck

The only hypothesis left explicit here is `FixedStemPigeonhole`: the geometric
pigeonhole theorem for a literal stem. A3 transfers it to an arbitrary stem
at its original depth, and the abstract library then gives the literal published
Ellentuck-topology conclusion.

This file deliberately keeps the geometric fixed-stem theorem as an
explicit parameter, so that the A3 transfer and abstract Ellentuck assembly
can be audited independently.  The parameter is discharged in
`A4ReviewComplete`, whose `fatTreeA4` and `fatTreeEllentuck` endpoints
are unconditional.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- The geometric pigeonhole statement for a literal finite stem. This is
an explicit proof obligation, not an axiom or an assumed instance. -/
def FixedStemPigeonhole : Prop :=
  ∀ (y : FiniteFatTree H) (U : FatTree H), ExtendsStem H y U →
    ∀ O : Set (AM H y.terminalCut 1),
      ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
        ((∀ g, OneBlockOccurs H y V g → g ∈ O) ∨
         (∀ g, OneBlockOccurs H y V g → g ∉ O))

/-- A3 transfers literal-stem homogeneity to the original depth cone. No
new pigeonhole assumption is introduced by the transfer. -/
theorem typed_pigeonhole_of_fixedStem
    (hP : FixedStemPigeonhole H)
    {n : Nat} (a : (approximationSystem H).Approx n)
    (B : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a B d)
    (O : Set ((approximationSystem H).Approx (n + 1))) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d B ∧
      ((approximationSystem H).oneStepApproximations a V ⊆ O ∨
        Disjoint ((approximationSystem H).oneStepApproximations a V) O) := by
  have hBB : B ∈ (approximationSystem H).levelNeighborhood d B :=
    ⟨reduces_refl H B, rfl⟩
  obtain ⟨U, hUaB⟩ := typed_amalgamation_nonempty H a B hd hBB
  have hU := (mem_neighborhood_iff_inNeighborhood H a B U).1 hUaB
  let Orow : Set (AM H a.1.terminalCut 1) :=
    {g | appendApprox H a g ∈ O}
  obtain ⟨A, hAU, haA, hhom⟩ := hP a.1 U hU.2 Orow
  have hAaB : A ∈ (approximationSystem H).neighborhood a B :=
    (mem_neighborhood_iff_inNeighborhood H a B A).2
      ⟨reduces_trans H hAU hU.1, haA⟩
  obtain ⟨V, hVB, hsub⟩ :=
    typed_amalgamation_refine_standard H a B hd hAaB
  have hfront : (approximationSystem H).oneStepApproximations a V ⊆
      (approximationSystem H).oneStepApproximations a A := by
    rintro b ⟨X, hXaV, hXb⟩
    exact ⟨X, hsub hXaV, hXb⟩
  refine ⟨V, hVB, ?_⟩
  rcases hhom with hyes | hno
  · left
    intro b hb
    obtain ⟨g, hg, hbg⟩ := oneStep_exists_appendedRow H a A (hfront hb)
    have hbEq : b = appendApprox H a g := Subtype.ext hbg
    rw [hbEq]
    exact hyes g hg
  · right
    rw [Set.disjoint_left]
    intro b hb hbO
    obtain ⟨g, hg, hbg⟩ := oneStep_exists_appendedRow H a A (hfront hb)
    have hbEq : b = appendApprox H a g := Subtype.ext hbg
    have hgO : g ∈ Orow := by
      change appendApprox H a g ∈ O
      rwa [hbEq] at hbO
    exact hno g hg hgO

/-- The A1--A4 instance once the explicit geometric obligation is supplied. -/
noncomputable def ramseySpaceOfFixedStemPigeonhole
    (hP : FixedStemPigeonhole H) :
    RamseySpace.AbstractRamseySpace (approximationSystem H) :=
  RamseySpace.AbstractRamseySpace.ofPublishedAxioms
    (finitization H)
    (typed_amalgamation_nonempty H)
    (typed_amalgamation_refine_published H)
    (typed_pigeonhole_of_fixedStem H hP)

/-- Conditional integration endpoint in the literal basic-neighbourhood
formulation. This checks the application interface of the abstract theorem. -/
theorem ellentuck_of_fixedStemPigeonhole
    (hP : FixedStemPigeonhole H) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := approximationSystem H) :=
  RamseySpace.abstractEllentuck_textbook
    (ramseySpaceOfFixedStemPigeonhole H hP) (isTychonoffClosed H)

end SuccessorTree.SMTree.FatTree
