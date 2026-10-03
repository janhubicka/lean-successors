import SuccessorTree.FatTree.Lift

/-!
# The fat-subtree reduction witness

This file begins the formalization of Definition `def:subfatsubtrees`.
Only the infinite-height relation is bundled here.  The finite relation must
also remember the terminal cut; it will be added before the Ramsey-space A.1/A.2
interface is declared.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A witness that `V` is a fat subtree of `U`, for infinite fat trees.
The local inclusion is exactly the manuscript's
`Lift_V(i,i+1) ⊆ Lift_U(φ(i),φ(i+1))`. -/
structure ReductionWitness (V U : FatTree H) where
  index : Nat → Nat
  index_strict : StrictMono index
  cut_eq : ∀ i : Nat, V.cut i = U.cut (index i)
  lift_subset : ∀ i : Nat,
    V.oneLift H i (TreeLevel (T := T) (V.cut i)) ⊆
      U.liftTo H (index i) (index (i + 1))
        (Nat.le_of_lt (index_strict (Nat.lt_succ_self i)))
        (TreeLevel (T := T) (U.cut (index i)))

/-- Infinite fat-subtree reduction. -/
def Reduces (V U : FatTree H) : Prop :=
  Nonempty (ReductionWitness H V U)

namespace ReductionWitness

/-- Alignment of the zeroth cut forces every reduction witness to start at
zero; this does not need to be a separate field in the definition. -/
theorem index_zero {V U : FatTree H}
    (w : ReductionWitness H V U) : w.index 0 = 0 := by
  apply U.cut_injective H
  calc
    U.cut (w.index 0) = V.cut 0 := (w.cut_eq 0).symm
    _ = 0 := V.cut_zero
    _ = U.cut 0 := U.cut_zero.symm

/-- Identity is a reduction witness. -/
def refl (U : FatTree H) : ReductionWitness H U U where
  index := fun i => i
  index_strict := by
    intro i j hij
    exact hij
  cut_eq := by
    intro i
    rfl
  lift_subset := by
    intro i
    rw [U.liftTo_succ H i (TreeLevel (T := T) (U.cut i))]

end ReductionWitness

/-- The infinite fat-subtree relation is reflexive. -/
theorem reduces_refl (U : FatTree H) : Reduces H U U :=
  ⟨ReductionWitness.refl H U⟩

end FatTree

end SMTree
end SuccessorTree
