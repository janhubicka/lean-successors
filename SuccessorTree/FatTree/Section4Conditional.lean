import SuccessorTree.FatTree.RelativeCategory
import SuccessorTree.FatTree.RelativeEA
import SuccessorTree.RamseySpace.Closed

/-!
# Full relative Ellentuck conclusion from the source EA1 + EA2 clauses

The common witness [a,U] is crucial: category preservation is given
only on that *open* fat neighbourhood, not on the whole fat-tree
space. We therefore apply fat Ellentuck to the restricted pullback
C ∩ rho⁻¹(X), and only then use EA1 to cover the selected algebraic
right-composition cone.

Both clauses remain explicit abstract hypotheses. No application
monoid is assumed to satisfy EA, and no false quotient/projection
identity is used.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- Source EA2: open target pullbacks are Baire in the relative fat
neighbourhood, and nowhere-dense target pullbacks are meagre there. -/
def HasRelativeEA2 {n : Nat}
    (a : (approximationSystem H).Approx n)
    (U : FatTree H) (rho : FatTree H → MMap H) : Prop :=
  let C : Set (FatTree H) := (approximationSystem H).neighborhood a U
  (∀ O : Set (MMap H),
      @IsOpen (MMap H) (ramseyApproximationSystem H).ellentuckTopology O →
      @BaireMeasurableSet C
        (TopologicalSpace.induced (Subtype.val : C → FatTree H)
          (approximationSystem H).ellentuckTopology)
        {W : C | rho W.1 ∈ O}) ∧
  (∀ N : Set (MMap H),
      @IsNowhereDense (MMap H) (ramseyApproximationSystem H).ellentuckTopology N →
      @_root_.IsMeagre C
        (TopologicalSpace.induced (Subtype.val : C → FatTree H)
          (approximationSystem H).ellentuckTopology)
        {W : C | rho W.1 ∈ N})

/-- Every monoid Ellentuck-Baire set has a homogeneous entire algebraic
cone, assuming EA1 cone coverage and EA2 on the same fat witness. -/
theorem coneRamsey_of_relativeEA2
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (hne : ((approximationSystem H).neighborhood a U).Nonempty)
    (rho : FatTree H → MMap H)
    (pure : Set (MMap H))
    (cone : MMap H → Set (MMap H))
    (hLift : ∀ V,
      V ∈ (approximationSystem H).levelNeighborhood d U →
      ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
        cone F' ⊆ rho '' ((approximationSystem H).neighborhood a V))
    (hEA2 : HasRelativeEA2 H a U rho)
    (X : Set (MMap H))
    (hX : @BaireMeasurableSet (MMap H)
      (ramseyApproximationSystem H).ellentuckTopology X) :
    ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
      (cone F' ⊆ X ∨ Disjoint (cone F') X) := by
  let R := approximationSystem H
  let C : Set (FatTree H) := R.neighborhood a U
  letI : TopologicalSpace (FatTree H) := R.ellentuckTopology
  letI : TopologicalSpace (MMap H) :=
    (ramseyApproximationSystem H).ellentuckTopology
  dsimp [HasRelativeEA2] at hEA2
  rcases hEA2 with ⟨hOpen, hND⟩
  have hCOpen : IsOpen C := R.isOpen_neighborhood a U
  have hReg : BaireMeasurableSet (C ∩ rho ⁻¹' X) :=
    SuccessorTree.RelativeCategory.baire_of_relative_EA2
      C hCOpen rho hOpen hND X hX
  obtain ⟨B, hBU, hHom⟩ :=
    (fatTreeEllentuck H).1 (C ∩ rho ⁻¹' X) hReg a U hne
  obtain ⟨V, hVU, hSub⟩ :=
    pureDepthRefine_of_basicMember H a U hd B hBU
  obtain ⟨F', hPure, hConeNonempty, hCover⟩ := hLift V hVU
  refine ⟨F', hPure, hConeNonempty, ?_⟩
  rcases hHom with hIn | hOut
  · left
    intro G hG
    obtain ⟨W, hW, hWMap⟩ := hCover hG
    have hWX : rho W ∈ X := (hIn (hSub hW)).2
    rwa [hWMap] at hWX
  · right
    rw [Set.disjoint_left]
    intro G hG hGX
    obtain ⟨W, hW, hWMap⟩ := hCover hG
    have hWC : W ∈ C := R.neighborhood_mono hBU.1 (hSub hW)
    have hWin : W ∈ C ∩ rho ⁻¹' X :=
      ⟨hWC, by simpa [hWMap] using hGX⟩
    exact (Set.disjoint_left.mp hOut) (hSub hW) hWin

/-- The meagre/Ramsey-null half, again with the common relative
EA1+EA2 witness and no global preimage-preservation premise. -/
theorem coneNull_of_relativeEA2
    {n : Nat} (a : (approximationSystem H).Approx n)
    (U : FatTree H) {d : Nat}
    (hd : (finitization H).HasDepth a U d)
    (hne : ((approximationSystem H).neighborhood a U).Nonempty)
    (rho : FatTree H → MMap H)
    (pure : Set (MMap H))
    (cone : MMap H → Set (MMap H))
    (hLift : ∀ V,
      V ∈ (approximationSystem H).levelNeighborhood d U →
      ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
        cone F' ⊆ rho '' ((approximationSystem H).neighborhood a V))
    (hEA2 : HasRelativeEA2 H a U rho)
    (X : Set (MMap H))
    (hX : @_root_.IsMeagre (MMap H)
      (ramseyApproximationSystem H).ellentuckTopology X) :
    ∃ F' : MMap H, F' ∈ pure ∧ (cone F').Nonempty ∧
      Disjoint (cone F') X := by
  let R := approximationSystem H
  let C : Set (FatTree H) := R.neighborhood a U
  letI : TopologicalSpace (FatTree H) := R.ellentuckTopology
  letI : TopologicalSpace (MMap H) :=
    (ramseyApproximationSystem H).ellentuckTopology
  dsimp [HasRelativeEA2] at hEA2
  rcases hEA2 with ⟨_, hND⟩
  have hReg : IsMeagre (C ∩ rho ⁻¹' X) :=
    SuccessorTree.RelativeCategory.meagre_of_relative_EA2
      C rho hND X hX
  obtain ⟨B, hBU, hDis⟩ :=
    (fatTreeEllentuck H).2 (C ∩ rho ⁻¹' X) hReg a U hne
  obtain ⟨V, hVU, hSub⟩ :=
    pureDepthRefine_of_basicMember H a U hd B hBU
  obtain ⟨F', hPure, hConeNonempty, hCover⟩ := hLift V hVU
  refine ⟨F', hPure, hConeNonempty, ?_⟩
  rw [Set.disjoint_left]
  intro G hG hGX
  obtain ⟨W, hW, hWMap⟩ := hCover hG
  have hWC : W ∈ C := R.neighborhood_mono hBU.1 (hSub hW)
  have hWin : W ∈ C ∩ rho ⁻¹' X :=
    ⟨hWC, by simpa [hWMap] using hGX⟩
  exact (Set.disjoint_left.mp hDis) (hSub hW) hWin

end SuccessorTree.SMTree.FatTree
