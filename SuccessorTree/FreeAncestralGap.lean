import SuccessorTree.FreeAncestralSuccessor
import Mathlib.Tactic

/-! # One-gap level shifts for free ancestral codes

These helpers implement the level transformation associated with inserting one
target level at m: levels below m stay fixed and levels at or above m move up
by one.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- Insert one gap at m in a source level below n. -/
def shiftFin (m n : Nat) (i : Fin n) : Fin (n + 1) :=
  if hi : i.val < m then
    ⟨i.val, Nat.lt.step i.isLt⟩
  else
    ⟨i.val + 1, by omega⟩

@[simp] theorem shiftFin_val_of_lt
    {m n : Nat} (i : Fin n) (hi : i.val < m) :
    (shiftFin m n i).val = i.val := by
  simp [shiftFin, hi]

@[simp] theorem shiftFin_val_of_ge
    {m n : Nat} (i : Fin n) (hi : m ≤ i.val) :
    (shiftFin m n i).val = i.val + 1 := by
  simp [shiftFin, Nat.not_lt.mpr hi]

/-- Shift every ancestral parameter level across one inserted gap. -/
def shiftParamTuple (m : Nat) {n : Nat}
    (t : ParamTuple arity n) :
    ParamTuple arity (n + 1) where
  len := t.len
  value := fun j => shiftFin m n (t.value j)

@[simp] theorem shiftParamTuple_len
    (m : Nat) {n : Nat} (t : ParamTuple arity n) :
    (shiftParamTuple m t).len = t.len := rfl

/-- Shift an intrinsic transition code across one inserted gap. -/
def shiftCode (m : Nat) {n : Nat}
    (c : Code Label arity n) :
    Code Label arity (n + 1) where
  label := c.label
  params := shiftParamTuple m c.params

@[simp] theorem shiftCode_label
    (m : Nat) {n : Nat} (c : Code Label arity n) :
    (shiftCode m c).label = c.label := rfl

@[simp] theorem shiftCode_params
    (m : Nat) {n : Nat} (c : Code Label arity n) :
    (shiftCode m c).params = shiftParamTuple m c.params := rfl

end FreeAncestral
end SuccessorTree
