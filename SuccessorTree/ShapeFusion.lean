import SuccessorTree.Canonical

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
    (hF : F.FusionStable H) : MMap H where
  map := ShapeMap.fusionLimit (fun i => (F i).map) hF
  mem := H.fusion_mem
    (fun i => (F i).map)
    (fun i => (F i).mem)
    hF

@[simp] theorem fusionLimit_apply
    (H : SMTree S) (F : Nat → MMap H)
    (hF : F.FusionStable H) (a : T) :
    MMap.fusionLimit H F hF a =
      F (LevelTree.lev a) a := rfl

/-- The M-map fusion limit agrees with any sufficiently late frozen stage. -/
theorem fusionLimit_eq_stage
    (H : SMTree S) (F : Nat → MMap H)
    (hF : F.FusionStable H)
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

/-- A sequence built by ordinary fusion steps satisfies the pointwise
stability hypothesis of M1. -/
theorem fusionStable_of_steps
    (H : SMTree S) (F : Nat → MMap H)
    (hstep : ∀ i : Nat, FusionStep H i (F i) (F (i + 1))) :
    F.FusionStable H := by
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

end SMTree
end SuccessorTree
