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


/-- Numerical level shift associated with one inserted gap. -/
def shiftNat (m k : Nat) : Nat :=
  if k < m then k else k + 1

theorem shiftNat_injective (m : Nat) :
    Function.Injective (shiftNat m) := by
  intro i j hij
  unfold shiftNat at hij
  by_cases hi : i < m <;> by_cases hj : j < m <;>
    simp [hi, hj] at hij ⊢ <;> omega

theorem list_map_injective_of_injective
    {α β : Type*} {g : α → β}
    (hg : Function.Injective g) :
    Function.Injective (List.map g) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.map_cons] at h
          have hxy : g x = g y := (List.cons.inj h).1
          have htail : List.map g xs = List.map g ys :=
            (List.cons.inj h).2
          have hxy' : x = y := hg hxy
          have htail' : xs = ys := ih htail
          simp [hxy', htail']

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


/-- Include an old ancestral level into a later source level. -/
def liftFin {n m : Nat} (h : n ≤ m) (i : Fin n) : Fin m :=
  ⟨i.val, lt_of_lt_of_le i.isLt h⟩

@[simp] theorem liftFin_val
    {n m : Nat} (h : n ≤ m) (i : Fin n) :
    (liftFin h i).val = i.val := rfl

/-- Reuse the same ancestral parameter levels at a later base level. -/
def liftParamTuple {n m : Nat} (h : n ≤ m)
    (t : ParamTuple arity n) :
    ParamTuple arity m where
  len := t.len
  value := fun j => liftFin h (t.value j)

@[simp] theorem liftParamTuple_len
    {n m : Nat} (h : n ≤ m)
    (t : ParamTuple arity n) :
    (liftParamTuple h t).len = t.len := rfl

/-- Reuse one intrinsic transition code at a later base level. -/
def liftCode {n m : Nat} (h : n ≤ m)
    (c : Code Label arity n) :
    Code Label arity m where
  label := c.label
  params := liftParamTuple h c.params

@[simp] theorem liftCode_label
    {n m : Nat} (h : n ≤ m)
    (c : Code Label arity n) :
    (liftCode h c).label = c.label := rfl

@[simp] theorem liftCode_params
    {n m : Nat} (h : n ≤ m)
    (c : Code Label arity n) :
    (liftCode h c).params = liftParamTuple h c.params := rfl

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


theorem levelList_shiftParamTuple
    (m : Nat) {n : Nat} (t : ParamTuple arity n) :
    levelList (shiftParamTuple m t) =
      (levelList t).map (shiftNat m) := by
  simp only [levelList, shiftParamTuple, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  by_cases hj : (t.value j).val < m
  · simp [shiftNat, shiftFin, hj, Function.comp_def]
  · simp [shiftNat, shiftFin, hj, Function.comp_def]

theorem shiftParamTuple_injective
    (m : Nat) {n : Nat} :
    Function.Injective
      (shiftParamTuple (arity := arity) m :
        ParamTuple arity n → ParamTuple arity (n + 1)) := by
  intro t u htu
  apply levelList_injective
  have hlevels :=
    congrArg (levelList (arity := arity)) htu
  rw [levelList_shiftParamTuple, levelList_shiftParamTuple] at hlevels
  exact
    list_map_injective_of_injective
      (shiftNat_injective m) hlevels

theorem shiftCode_injective
    (m : Nat) {n : Nat} :
    Function.Injective
      (shiftCode (Label := Label) (arity := arity) m :
        Code Label arity n → Code Label arity (n + 1)) := by
  intro c d h
  cases c with
  | mk cl cp =>
      cases d with
      | mk dl dp =>
          have hl : cl = dl := by
            exact congrArg Code.label h
          have hp :
              shiftParamTuple m cp =
                shiftParamTuple m dp := by
            exact congrArg Code.params h
          have hpeq : cp = dp :=
            shiftParamTuple_injective m hp
          subst dl
          subst dp
          rfl

end FreeAncestral
end SuccessorTree
