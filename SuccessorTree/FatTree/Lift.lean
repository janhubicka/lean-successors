import SuccessorTree.FatTree.Basic

/-!
# Lift along a fat subtree

This is the recursive `Lift_U(X,k)` operation from the manuscript.  We keep
its source index explicit in Lean; the paper can infer it from the level on
which `X` lives because the cut is strictly increasing.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Nodes on one tree level. -/
def TreeLevel (n : Nat) : Set T :=
  {x | LevelTree.lev x = n}

/-- Immediate successors of members of a set. -/
def ImmediateSuccessors (X : Set T) : Set T :=
  {y | ∃ x ∈ X, x ⋖ y}

namespace FatTree

variable (H : SMTree S)

/-- Immediate successors of a set on level `n` lie on level `n+1`. -/
theorem immediateSuccessors_subset_level
    {n : Nat} {X : Set T} (hX : X ⊆ TreeLevel (T := T) n) :
    ImmediateSuccessors (T := T) X ⊆ TreeLevel (T := T) (n + 1) := by
  intro y hy
  rcases hy with ⟨x, hxX, hxy⟩
  have hx : LevelTree.lev x = n := hX hxX
  change LevelTree.lev y = n + 1
  calc
    LevelTree.lev y = LevelTree.lev x + 1 := LevelTree.covBy_level_eq hxy
    _ = n + 1 := by rw [hx]

/-- One step of the manuscript's lift operation. -/
noncomputable def oneLift (U : FatTree H) (i : Nat) (X : Set T) : Set T :=
  U.rowExtension H i '' ImmediateSuccessors (T := T) X

/-- The parenthetical level claim in Definition `def:lift`. -/
theorem oneLift_subset_nextLevel (U : FatTree H) (i : Nat)
    {X : Set T} (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.oneLift H i X ⊆ TreeLevel (T := T) (U.cut (i + 1)) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have hzlev : LevelTree.lev z = U.cut i + 1 :=
    immediateSuccessors_subset_level hX hz
  change LevelTree.lev (U.rowExtension H i z) = U.cut (i + 1)
  calc
    LevelTree.lev (U.rowExtension H i z) =
        H.levelMap (U.rowExtension H i).map (LevelTree.lev z) :=
      (H.levelMap_eq (U.rowExtension H i).map (a := z)).symm
    _ = H.levelMap (U.rowExtension H i).map (U.cut i + 1) := by rw [hzlev]
    _ = U.cut (i + 1) := U.rowExtension_level_succ H i

/-- Iterate the one-step lift for a prescribed number of fat-tree rows. -/
noncomputable def liftSteps (U : FatTree H) :
    (i steps : Nat) → Set T → Set T
  | _, 0, X => X
  | i, steps + 1, X =>
      liftSteps U (i + 1) steps (U.oneLift H i X)

@[simp] theorem liftSteps_zero (U : FatTree H) (i : Nat) (X : Set T) :
    U.liftSteps H i 0 X = X := rfl

@[simp] theorem liftSteps_succ (U : FatTree H)
    (i steps : Nat) (X : Set T) :
    U.liftSteps H i (steps + 1) X =
      U.liftSteps H (i + 1) steps (U.oneLift H i X) := rfl

/-- Lifting preserves the intended cut level. -/
theorem liftSteps_subset_level (U : FatTree H)
    (i steps : Nat) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.liftSteps H i steps X ⊆
      TreeLevel (T := T) (U.cut (i + steps)) := by
  induction steps generalizing i X with
  | zero =>
      simpa using hX
  | succ steps ih =>
      have hnext : U.oneLift H i X ⊆
          TreeLevel (T := T) (U.cut (i + 1)) :=
        U.oneLift_subset_nextLevel H i hX
      have hrec := ih (i := i + 1) (X := U.oneLift H i X) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-- Paper notation `Lift_U(X,k)`, with the source cut `i` explicit. -/
noncomputable def liftTo (U : FatTree H)
    (i k : Nat) (hik : i ≤ k) (X : Set T) : Set T :=
  U.liftSteps H i (k - i) X

/-- Lifting across exactly one fat-tree row is the one-step lift. -/
theorem liftTo_succ (U : FatTree H) (i : Nat) (X : Set T) :
    U.liftTo H i (i + 1) (by omega) X = U.oneLift H i X := by
  unfold liftTo
  have hsub : i + 1 - i = 1 := by omega
  rw [hsub, liftSteps_succ, liftSteps_zero]

/-- The explicit-source version of the lift lands on the target cut. -/
theorem liftTo_subset_level (U : FatTree H)
    (i k : Nat) (hik : i ≤ k) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.liftTo H i k hik X ⊆ TreeLevel (T := T) (U.cut k) := by
  change U.liftSteps H i (k - i) X ⊆ TreeLevel (T := T) (U.cut k)
  have h := U.liftSteps_subset_level H i (k - i) hX
  have hidx : i + (k - i) = k := by omega
  simpa [hidx] using h

/-- The empty set stays empty under lifting. -/
@[simp] theorem oneLift_empty (U : FatTree H) (i : Nat) :
    U.oneLift H i (∅ : Set T) = ∅ := by
  ext y
  simp [oneLift, ImmediateSuccessors]

@[simp] theorem liftSteps_empty (U : FatTree H) (i steps : Nat) :
    U.liftSteps H i steps (∅ : Set T) = ∅ := by
  induction steps generalizing i with
  | zero => rfl
  | succ steps ih =>
      rw [liftSteps_succ, oneLift_empty]
      exact ih (i + 1)

end FatTree

end SMTree
end SuccessorTree
