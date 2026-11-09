import SuccessorTree.FatTree.BorelImage
import SuccessorTree.FatTree.Sequencing
import SuccessorTree.FatTree.ApproximationSystem
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Constructions
import Mathlib.Tactic

/-!
# Pointwise-Borel colourings of the canonical fat-tree image

The pointwise convergence topology of the algebraic shape monoid is
the initial topology of its evaluations on discrete tree nodes.
The carried shape map is locally constant on each coordinate: a
node of level n sees only the first n+1 fat-tree rows.

Thus every pointwise-Borel colour fibre pulls back to a Baire set in
the fat-tree Ellentuck topology. Combined with the separately checked
fat-tree Ellentuck theorem this gives the unconditional finite-colour
fat-image theorem from the corrected manuscript, *not* homogeneity
on an algebraic right-composition cone.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- Equal finite initial fat subtrees have the same total canonical
extension of their last row. This uses equality of actual rows, not
an unproved algebraic factoring of fat refinements. -/
theorem rowExtension_eq_of_samePrefix
    (U V : FatTree H) (i : Nat)
    (h : U.initialSegment H (i + 1) = V.initialSegment H (i + 1)) :
    U.rowExtension H i = V.rowExtension H i := by
  let rowAt (A : FiniteFatTree H) : MMap H :=
    if hi : i < A.height then A.rowExtension H ⟨i, hi⟩ else MMap.id H
  have hh : rowAt (U.initialSegment H (i + 1)) =
      rowAt (V.initialSegment H (i + 1)) := congrArg rowAt h
  have hU : rowAt (U.initialSegment H (i + 1)) =
      U.rowExtension H i := by
    simp [rowAt, FatTree.initialSegment,
      FiniteFatTree.rowExtension, FatTree.rowExtension]
  have hV : rowAt (V.initialSegment H (i + 1)) =
      V.rowExtension H i := by
    simp [rowAt, FatTree.initialSegment,
      FiniteFatTree.rowExtension, FatTree.rowExtension]
  exact hU.symm.trans (hh.trans hV)

/-- Finite products of canonical rows are determined by their finite
fat-tree stem, even though total right-composition reductions are not. -/
theorem partialMap_eq_of_samePrefix :
    ∀ n (U V : FatTree H),
      U.initialSegment H n = V.initialSegment H n →
      partialMap H U n = partialMap H V n := by
  intro n
  induction n with
  | zero =>
      intro U V _
      rfl
  | succ n ih =>
      intro U V h
      have hp : U.initialSegment H n = V.initialSegment H n :=
        (a1_three H h).2 n (Nat.lt_succ_self n)
      calc
        partialMap H U (n + 1) =
            MMap.comp H (U.rowExtension H n) (partialMap H U n) := rfl
        _ = MMap.comp H (V.rowExtension H n) (partialMap H V n) := by
          rw [rowExtension_eq_of_samePrefix H U V n h, ih U V hp]
        _ = partialMap H V (n + 1) := rfl

/-- An individual value of the associated algebraic map depends only
on the fat-tree stem through one more level than its source node. -/
theorem associatedMap_eq_of_samePrefix
    (U V : FatTree H) (x : T)
    (h : U.initialSegment H (LevelTree.lev x + 1) =
        V.initialSegment H (LevelTree.lev x + 1)) :
    associatedMap H U x = associatedMap H V x := by
  rw [associatedMap_apply H U x, associatedMap_apply H V x]
  exact congrArg (fun F : MMap H => F x)
    (partialMap_eq_of_samePrefix H (LevelTree.lev x + 1) U V h)

/-- Every pointwise evaluation fibre of the fat-tree associated map
is Ellentuck-open. This is weaker than asserting Ellentuck-continuity
into the *monoid Ellentuck topology*. -/
theorem isOpen_associatedMap_eval_fibre
    (x : T) (y : T) :
    @IsOpen (FatTree H) (approximationSystem H).ellentuckTopology
      {U | associatedMap H U x = y} := by
  change (approximationSystem H).IsEllentuckOpen
    {U | associatedMap H U x = y}
  intro U hU
  let n := LevelTree.lev x + 1
  let a : (approximationSystem H).Approx n := exactApprox H n U
  refine ⟨n, a, U, ?_, ?_⟩
  · exact ⟨(approximationSystem H).le_refl U, rfl⟩
  · intro V hV
    have hEq : exactApprox H n V = exactApprox H n U := hV.2
    have hPrefix : V.initialSegment H n = U.initialSegment H n :=
      congrArg Subtype.val hEq
    exact (associatedMap_eq_of_samePrefix H V U x hPrefix).trans hU

section Pointwise

/-- The target tree is discrete in the pointwise function topology. -/
local instance : TopologicalSpace T := ⊥
local instance : DiscreteTopology T := ⟨rfl⟩

/-- Each coordinate of the carried map is continuous from fat
Ellentuck to the discrete tree. -/
theorem continuous_associatedMap_eval (x : T) :
    @Continuous (FatTree H) T
      (approximationSystem H).ellentuckTopology (⊥ : TopologicalSpace T)
      (fun U => associatedMap H U x) := by
  letI : TopologicalSpace (FatTree H) :=
    (approximationSystem H).ellentuckTopology
  apply continuous_def.mpr
  intro A _
  have hUnion :
      {U : FatTree H | associatedMap H U x ∈ A} =
        ⋃ y : A, {U : FatTree H | associatedMap H U x = y.1} := by
    ext U
    constructor
    · intro hU
      exact Set.mem_iUnion.mpr
        ⟨⟨associatedMap H U x, hU⟩, rfl⟩
    · intro hU
      rcases Set.mem_iUnion.mp hU with ⟨y, hEq⟩
      change associatedMap H U x = (y : T) at hEq
      change associatedMap H U x ∈ A
      rw [hEq]
      exact y.property
  change IsOpen {U : FatTree H | associatedMap H U x ∈ A}
  rw [hUnion]
  exact isOpen_iUnion (fun y : A =>
    isOpen_associatedMap_eval_fibre H x y.1)

/-- The actual pointwise topology of the map family, induced by the
embedding into the product of discrete tree coordinates. -/
noncomputable def pointwiseTopology : TopologicalSpace (MMap H) :=
  TopologicalSpace.induced
    (fun F : MMap H => (fun x : T => F x))
    (inferInstance : TopologicalSpace (T → T))

/-- The associated-map projection is continuous from fat Ellentuck to
the pointwise topology, but need not be continuous into the monoid
Ellentuck topology. -/
theorem associatedMap_pointwiseContinuous :
    @Continuous (FatTree H) (MMap H)
      (approximationSystem H).ellentuckTopology
      (pointwiseTopology H) (associatedMap H) := by
  letI : TopologicalSpace (FatTree H) :=
    (approximationSystem H).ellentuckTopology
  change @Continuous (FatTree H) (MMap H)
    (approximationSystem H).ellentuckTopology
    (TopologicalSpace.induced
      (fun F : MMap H => (fun x : T => F x))
      (inferInstance : TopologicalSpace (T → T)))
    (associatedMap H)
  apply continuous_induced_rng.mpr
  exact continuous_pi (fun x => continuous_associatedMap_eval H x)

/-- The induced Borel sigma algebra of pointwise convergence. -/
noncomputable def pointwiseBorel : MeasurableSpace (MMap H) :=
  letI : TopologicalSpace (MMap H) := pointwiseTopology H
  borel (MMap H)

/-- Fully unconditional Borel-colouring theorem on fat-tree images.
The target algebraic cone is deliberately NOT asserted homogeneous. -/
theorem fatImageHomogeneous_of_pointwiseBorel
    {κ : Type w} [Fintype κ]
    {n : Nat} (a : (approximationSystem H).Approx n)
    (A : FatTree H)
    (hne : ((approximationSystem H).neighborhood a A).Nonempty)
    (colour : MMap H → κ)
    (hBorel : ∀ c : κ,
      @MeasurableSet (MMap H) (pointwiseBorel H)
        {F | colour F = c}) :
    ∃ B, B ∈ (approximationSystem H).neighborhood a A ∧
      ∃ c : κ, ∀ U,
        U ∈ (approximationSystem H).neighborhood a B →
          colour (associatedMap H U) = c := by
  have hBaire : ∀ c : κ,
      @BaireMeasurableSet (FatTree H)
        (approximationSystem H).ellentuckTopology
        {U | colour (associatedMap H U) = c} := by
    intro c
    letI : TopologicalSpace (FatTree H) :=
      (approximationSystem H).ellentuckTopology
    letI : TopologicalSpace (MMap H) := pointwiseTopology H
    letI : MeasurableSpace (FatTree H) := borel (FatTree H)
    letI : MeasurableSpace (MMap H) := pointwiseBorel H
    letI : BorelSpace (FatTree H) := ⟨rfl⟩
    letI : BorelSpace (MMap H) := ⟨rfl⟩
    have hmeas : Measurable (associatedMap H) :=
      (associatedMap_pointwiseContinuous H).measurable
    have hBorelC : MeasurableSet {F : MMap H | colour F = c} :=
      hBorel c
    have hMeasC :
        MeasurableSet {U : FatTree H | colour (associatedMap H U) = c} :=
      hBorelC.preimage hmeas
    exact hMeasC.baireMeasurableSet
  exact fatImageHomogeneous_of_BaireFibres H a A hne colour hBaire

end Pointwise

end SuccessorTree.SMTree.FatTree
