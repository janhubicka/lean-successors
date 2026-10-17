import SuccessorTree.FatTree.BorelImage
import SuccessorTree.FatTree.A3Typed
import RamseySpace.FiniteColouring
import RamseySpace.Standard

/-!
# Relative lifting of fat-tree Ramsey homogeneity to algebraic cones

The paper's EA1 is a *covering* assertion, not an equality between the
geometric fat refinement order and right-composition reductions. This
module isolates the genuine logical transfer after the Baire pullback
and the relative cone-lifting assumptions have been supplied.

EA2's topological preservation of Baire/meagre classes is not smuggled in:
the respective statements explicitly take Baire/meagre pullbacks as
hypotheses. No claim about a concrete monoid satisfying EA1 or EA2
is made here.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- Fat-tree A3(2) passes from a literal basic-neighbourhood member to
the original protected depth, without claiming that a geometrically
occurring stem is an initial segment of the ambient tree. -/
theorem pureDepthRefine_of_basicMember
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (B : FatTree H)
    (hBU : B ∈ (approximationSystem H).neighborhood a U) :
    ∃ V, V ∈ (approximationSystem H).levelNeighborhood d U ∧
      (approximationSystem H).neighborhood a V ⊆
        (approximationSystem H).neighborhood a B := by
  let R := approximationSystem H
  have hneB : (R.neighborhood a B).Nonempty :=
    ⟨B, R.le_refl B, hBU.2⟩
  obtain ⟨V, hVU, _, hsub⟩ :=
    typed_amalgamation_refine_published H a U hd hBU.1 hneB
  exact ⟨V, hVU, hsub⟩

/-- A finite Baire-measurable colouring is homogeneous on a whole
algebraic cone as soon as relative lifting covers that cone by an
appropriate homogeneous fat image. This is the formal EA1 transfer
step, parameterized over an abstract pure refinement family. -/
theorem coneHomogeneous_of_BairePullback_and_lifting
    {κ : Type w} [Fintype κ]
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (hne : ((approximationSystem H).neighborhood a U).Nonempty)
    (ρ : FatTree H → MMap H)
    (pure : Set (MMap H))
    (cone : MMap H → Set (MMap H))
    (hLift : ∀ V,
      V ∈ (approximationSystem H).levelNeighborhood d U →
      ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
        cone F' ⊆ ρ '' ((approximationSystem H).neighborhood a V))
    (colour : MMap H → κ)
    (hBaire : ∀ c : κ,
      @BaireMeasurableSet (FatTree H)
        (approximationSystem H).ellentuckTopology
        {V | colour (ρ V) = c}) :
    ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
      ∃ c : κ, ∀ G ∈ cone F', colour G = c := by
  obtain ⟨B, hBU, c, hmono⟩ :=
    RamseySpace.finiteBaireColouring (fatTreeEllentuck H)
      a U hne (fun V => colour (ρ V)) hBaire
  obtain ⟨V, hVU, hsub⟩ :=
    pureDepthRefine_of_basicMember H a U hd B hBU
  obtain ⟨F', hF', hneCone, hcover⟩ := hLift V hVU
  refine ⟨F', hF', hneCone, c, ?_⟩
  intro G hG
  obtain ⟨W, hW, hWρ⟩ := hcover hG
  calc
    colour G = colour (ρ W) := congrArg colour hWρ.symm
    _ = c := hmono W (hsub hW)

/-- The Baire half of the conditional Ellentuck transfer. EA1 supplies
the covering property; the Baire pullback is made an explicit premise
rather than inferred from the generally false global projection identity. -/
theorem coneRamsey_of_BairePullback_and_lifting
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (hne : ((approximationSystem H).neighborhood a U).Nonempty)
    (ρ : FatTree H → MMap H)
    (pure : Set (MMap H))
    (cone : MMap H → Set (MMap H))
    (hLift : ∀ V,
      V ∈ (approximationSystem H).levelNeighborhood d U →
      ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
        cone F' ⊆ ρ '' ((approximationSystem H).neighborhood a V))
    (X : Set (MMap H))
    (hBaire : @BaireMeasurableSet (FatTree H)
      (approximationSystem H).ellentuckTopology {W | ρ W ∈ X}) :
    ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
      (cone F' ⊆ X ∨ Disjoint (cone F') X) := by
  obtain ⟨B, hBU, hhom⟩ :=
    (fatTreeEllentuck H).1 {W | ρ W ∈ X} hBaire a U hne
  obtain ⟨V, hVU, hsub⟩ :=
    pureDepthRefine_of_basicMember H a U hd B hBU
  obtain ⟨F', hF', hneCone, hcover⟩ := hLift V hVU
  refine ⟨F', hF', hneCone, ?_⟩
  rcases hhom with hIn | hOut
  · left
    intro G hG
    obtain ⟨W, hW, hWρ⟩ := hcover hG
    have hWin : ρ W ∈ X := hIn (hsub hW)
    rw [hWρ] at hWin
    exact hWin
  · right
    rw [Set.disjoint_left]
    intro G hG hGX
    obtain ⟨W, hW, hWρ⟩ := hcover hG
    have hWin : ρ W ∈ X := by rwa [hWρ]
    exact (Set.disjoint_left.mp hOut) (hsub hW) hWin

/-- The Ramsey-null half of the conditional Ellentuck transfer, assuming
the actual fat pullback is meagre. In the manuscript EA2 is precisely the
regularity clause used to obtain this pullback hypothesis locally. -/
theorem coneNull_of_meagrePullback_and_lifting
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (hne : ((approximationSystem H).neighborhood a U).Nonempty)
    (ρ : FatTree H → MMap H)
    (pure : Set (MMap H))
    (cone : MMap H → Set (MMap H))
    (hLift : ∀ V,
      V ∈ (approximationSystem H).levelNeighborhood d U →
      ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
        cone F' ⊆ ρ '' ((approximationSystem H).neighborhood a V))
    (X : Set (MMap H))
    (hMeagre : @_root_.IsMeagre (FatTree H)
      (approximationSystem H).ellentuckTopology {W | ρ W ∈ X}) :
    ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
      Disjoint (cone F') X := by
  obtain ⟨B, hBU, hhom⟩ :=
    (fatTreeEllentuck H).2 {W | ρ W ∈ X} hMeagre a U hne
  obtain ⟨V, hVU, hsub⟩ :=
    pureDepthRefine_of_basicMember H a U hd B hBU
  obtain ⟨F', hF', hneCone, hcover⟩ := hLift V hVU
  refine ⟨F', hF', hneCone, ?_⟩
  rw [Set.disjoint_left]
  intro G hG hGX
  obtain ⟨W, hW, hWρ⟩ := hcover hG
  have hWin : ρ W ∈ X := by rwa [hWρ]
  exact (Set.disjoint_left.mp hhom) (hsub hW) hWin

end SuccessorTree.SMTree.FatTree
