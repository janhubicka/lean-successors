import SuccessorTree.HalesJewett.ForcingFusion
import Mathlib.Basic.Countable.Basic

/-!
# A concrete schedule of starred lines

The fusion proof now needs only a surjective enumeration of starred lines.
For a countable alphabet, starred lines are countable, so a surjection from
the natural numbers gives the schedule directly.
-/

namespace SuccessorTree
namespace HalesJewett

def lineSymbolEquivOption (α : Type u) : LineSymbol α ≃ Option α where
  toFun
    | .const a => some a
    | .parameter => none
  invFun
    | some a => .const a
    | none => .parameter
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance lineSymbolCountable [Countable α] :
    Countable (LineSymbol α) :=
  Countable.of_equiv (Option α) (lineSymbolEquivOption α).symm

theorem StarLine.word_injective :
    Function.Injective (fun L : StarLine α => L.word) := by
  intro L K h
  cases L with
  | mk w hw =>
      cases K with
      | mk v hv =>
          cases h
          rfl

noncomputable instance starLineCountable [Countable α] :
    Countable (StarLine α) :=
  StarLine.word_injective.countable

instance starLineNonempty : Nonempty (StarLine α) :=
  ⟨⟨[LineSymbol.parameter], by simp⟩⟩

noncomputable def countableLineSchedule [Countable α] : LineSchedule α := by
  obtain ⟨f, hf⟩ := exists_surjective_nat (StarLine α)
  exact ⟨f, hf⟩

theorem countableLineSchedule_covers [Countable α]
    (L : StarLine α) :
    ∃ i : Nat, (countableLineSchedule (α := α)).line i = L :=
  (countableLineSchedule (α := α)).covers L

end HalesJewett
end SuccessorTree
