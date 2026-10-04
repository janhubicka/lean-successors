import SuccessorTree.FatTree.Lift

/-!
# Finite fat-tree reduction witnesses

This is the finite-height half of Definition `def:subfatsubtrees`.
The cut map is defined on all `height + 1` cuts, including the terminal cut.
Thus the formal interface cannot silently omit the final-cut compatibility
needed later by the finitary order in Todorčević A.2.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- A witness that a finite fat tree `V` is a fat subtree of `U`.

The strictly increasing cut map is defined on every cut of `V`, including
its terminal cut.  The block condition is required only for actual rows. -/
structure ReductionWitness (V U : FiniteFatTree H) where
  index : Fin (V.height + 1) → Fin (U.height + 1)
  index_strict : StrictMono index
  cut_eq : ∀ i : Fin (V.height + 1), V.cut i = U.cut (index i)
  lift_subset : ∀ i : Fin V.height,
    V.oneLift H i
        (TreeLevel (T := T) (V.cut i.castSucc)) ⊆
      U.liftTo H (index i.castSucc) (index i.succ)
        (le_of_lt (index_strict
          (by
            change i.1 < i.1 + 1
            omega)))
        (TreeLevel (T := T) (U.cut (index i.castSucc)))

/-- Finite fat-subtree reduction. -/
def Reduces (V U : FiniteFatTree H) : Prop :=
  Nonempty (ReductionWitness H V U)

namespace ReductionWitness

/-- Identity is a finite reduction witness. -/
def refl (U : FiniteFatTree H) : ReductionWitness H U U where
  index := fun i => i
  index_strict := by
    intro i j hij
    exact hij
  cut_eq := by
    intro i
    rfl
  lift_subset := by
    intro i
    rw [U.liftTo_succ H i
      (TreeLevel (T := T) (U.cut i.castSucc))]

end ReductionWitness

/-- The finite fat-subtree relation is reflexive. -/
theorem reduces_refl (U : FiniteFatTree H) : Reduces H U U :=
  ⟨ReductionWitness.refl H U⟩

end FiniteFatTree

end SMTree
end SuccessorTree
