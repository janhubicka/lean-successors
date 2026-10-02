import SuccessorTree.Canonical
import SuccessorTree.RamseySpace.Basic
import SuccessorTree.RamseySpace.Finitization

/-!
# Ordinary fusion of shape-preserving M-maps

This is the Milliken-style fusion mechanism used for the direct
shape-preserving Ramsey theorem.  A refinement step at stage `i` is
right-composition by an M-map which fixes all source levels at most `i`.
Consequently each finite source level is eventually frozen, and M1 supplies
the pointwise fusion limit.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace MMap

/-- Stabilization of a sequence of M-maps in the sense required by M1. -/
def FusionStable (H : SMTree S) (F : Nat → MMap H) : Prop :=
  ShapeMap.FusionStable (fun i => (F i).map)

/-- The M1 fusion limit of a stable sequence of M-maps. -/
noncomputable def fusionLimit
    (H : SMTree S) (F : Nat → MMap H)
    (hF : MMap.FusionStable H F) : MMap H where
  map := ShapeMap.fusionLimit (fun i => (F i).map) hF
  mem := H.fusion_mem
    (fun i => (F i).map)
    (fun i => (F i).mem)
    hF

@[simp] theorem fusionLimit_apply
    (H : SMTree S) (F : Nat → MMap H)
    (hF : MMap.FusionStable H F) (a : T) :
    MMap.fusionLimit H F hF a =
      F (LevelTree.lev a) a := rfl

/-- The M-map fusion limit agrees with any sufficiently late frozen stage. -/
theorem fusionLimit_eq_stage
    (H : SMTree S) (F : Nat → MMap H)
    (hF : MMap.FusionStable H F)
    {i : Nat} {a : T} (ha : LevelTree.lev a ≤ i) :
    MMap.fusionLimit H F hF a = F i a := by
  exact ShapeMap.fusionLimit_eq_stage
    (fun j => (F j).map) hF ha

end MMap

/-- One ordinary fusion refinement step.  The new map is obtained by
right-composing the old one with a map that is the identity through level
`i`. -/
def FusionStep
    (H : SMTree S) (i : Nat)
    (F G : MMap H) : Prop :=
  ∃ K : MMap H,
    K.FixesBelow H (i + 1) ∧
      G = MMap.comp H F K

/-- A fusion step really preserves the frozen initial segment. -/
theorem fusionStep_agrees
    (H : SMTree S) {i : Nat} {F G : MMap H}
    (h : FusionStep H i F G)
    (a : T) (ha : LevelTree.lev a ≤ i) :
    G a = F a := by
  rcases h with ⟨K, hK, rfl⟩
  change F (K a) = F a
  rw [hK a (by omega)]

/-- A fusion step is exactly a refinement in the depth-(i+1)
neighborhood: it refines by right composition and preserves the whole source
segment through level i. -/
theorem fusionStep_mem_levelNeighborhood
    (H : SMTree S) {i : Nat} {F G : MMap H}
    (h : FusionStep H i F G) :
    G ∈ (ramseyApproximationSystem H).levelNeighborhood (i + 1) F := by
  rcases h with ⟨K, hK, rfl⟩
  constructor
  · refine ⟨K, ?_⟩
    intro a
    rfl
  · apply Subtype.ext
    funext a
    change F (K a.1) = F a.1
    rw [hK a.1 (by omega)]

/-- Conversely, every depth-(i+1) neighborhood refinement is an ordinary
fusion step.  Injectivity of the outer shape map forces the right factor to
be the identity on the frozen source segment. -/
theorem fusionStep_of_mem_levelNeighborhood
    (H : SMTree S) {i : Nat} {F G : MMap H}
    (hG :
      G ∈ (ramseyApproximationSystem H).levelNeighborhood (i + 1) F) :
    FusionStep H i F G := by
  rcases hG.1 with ⟨K, hK⟩
  refine ⟨K, ?_, ?_⟩
  · intro a ha
    apply F.map.injective
    have hprefix := congrArg Subtype.val hG.2
    change G.restrictLe H i = F.restrictLe H i at hprefix
    have hGa : G a = F a := by
      exact congrFun hprefix ⟨a, by omega⟩
    exact (hK a).symm.trans hGa
  · apply MMap.ext_apply
    intro a
    exact hK a

theorem fusionStep_iff_mem_levelNeighborhood
    (H : SMTree S) {i : Nat} {F G : MMap H} :
    FusionStep H i F G ↔
      G ∈ (ramseyApproximationSystem H).levelNeighborhood (i + 1) F :=
  ⟨H.fusionStep_mem_levelNeighborhood,
    H.fusionStep_of_mem_levelNeighborhood⟩

/-- A sequence built by ordinary fusion steps satisfies the pointwise
stability hypothesis of M1. -/
theorem fusionStable_of_steps
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1))) :
    MMap.FusionStable H F := by
  intro i a ha
  exact (H.fusionStep_agrees (hstep i) a ha).symm

/-- Package the ordinary fusion limit from its stepwise construction. -/
noncomputable def fusionOfSteps
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1))) :
    MMap H :=
  MMap.fusionLimit H F (H.fusionStable_of_steps F hstep)

@[simp] theorem fusionOfSteps_apply
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)))
    (a : T) :
    H.fusionOfSteps F hstep a =
      F (LevelTree.lev a) a := rfl

theorem fusionOfSteps_eq_stage
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)))
    {i : Nat} {a : T} (ha : LevelTree.lev a ≤ i) :
    H.fusionOfSteps F hstep a = F i a := by
  exact MMap.fusionLimit_eq_stage H F
    (H.fusionStable_of_steps F hstep) ha

/-- Every fusion step is a genuine Ramsey reduction. -/
theorem fusionStep_reduction
    (H : SMTree S) {i : Nat} {F G : MMap H}
    (h : FusionStep H i F G) :
    RamseyReduction H G F := by
  rcases h with ⟨K, hK, rfl⟩
  refine ⟨K, ?_⟩
  intro a
  rfl

/-- Later stages of an ordinary fusion sequence refine all earlier stages. -/
theorem fusionSteps_reduction_of_le
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)))
    {i j : Nat} (hij : i ≤ j) :
    RamseyReduction H (F j) (F i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero =>
      simpa using H.ramseyReduction_refl (F i)
  | succ d ih =>
      have hs :
          RamseyReduction H (F (i + d + 1)) (F (i + d)) := by
        convert H.fusionStep_reduction (hstep (i + d)) using 1 <;> omega
      exact H.ramseyReduction_trans hs (ih (by omega))

/-- The diagonal fusion limit has the same nth finite approximation as every
sufficiently late stage. -/
theorem fusionOfSteps_ramseyApprox_eq_stage
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)))
    {n i : Nat} (hni : n ≤ i + 1) :
    ramseyApprox H n (H.fusionOfSteps F hstep) =
      ramseyApprox H n (F i) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      apply Subtype.ext
      funext a
      change H.fusionOfSteps F hstep a.1 = F i a.1
      apply H.fusionOfSteps_eq_stage F hstep
      omega

/-- The ordinary fusion limit is a Ramsey refinement of every stage.  This is
proved purely from A2: each finite approximation of the limit is already a
finite approximation of a sufficiently late stage, and late stages refine
the chosen earlier stage. -/
theorem fusionOfSteps_reduction_stage
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)))
    (i : Nat) :
    RamseyReduction H (H.fusionOfSteps F hstep) (F i) := by
  apply H.reduction_of_ramseyLeFin_all
  intro n
  let j : Nat := i + n
  have hred : RamseyReduction H (F j) (F i) := by
    apply H.fusionSteps_reduction_of_le F hstep
    dsimp [j]
    omega
  obtain ⟨m, hm⟩ := H.ramseyLeFin_of_reduction hred n
  refine ⟨m, ?_⟩
  have heq :
      ramseyApprox H n (H.fusionOfSteps F hstep) =
        ramseyApprox H n (F j) := by
    apply H.fusionOfSteps_ramseyApprox_eq_stage F hstep
    dsimp [j]
    omega
  simpa [RamseySpace.ApproximationSystem.finiteApprox, heq] using hm

/-- In particular the fusion limit lies in the frozen neighborhood of every
stage. -/
theorem fusionOfSteps_mem_levelNeighborhood
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1)))
    (i : Nat) :
    H.fusionOfSteps F hstep ∈
      (ramseyApproximationSystem H).levelNeighborhood (i + 1) (F i) := by
  constructor
  · exact H.fusionOfSteps_reduction_stage F hstep i
  · exact H.fusionOfSteps_ramseyApprox_eq_stage F hstep le_rfl

end SMTree
end SuccessorTree
