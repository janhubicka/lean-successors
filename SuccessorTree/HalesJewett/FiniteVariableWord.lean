import SuccessorTree.HalesJewett.VariableWord
import Mathlib.Tactic

/-!
# Finite variable-word calculus

This file starts the finite-word layer needed for Lemma 1 of the
Hubička--Smolík forcing proof.  We use natural-numbered variables and an
evaluation which truncates at the first variable not supplied by the input
word.  This matches the paper's substitution convention.

The first verified facts are the two cases used when a new variable is
appended: with exactly `n` supplied letters a new `λ_n` acts as the star
truncation, while after supplying one more letter it acts as the ordinary line
evaluation.
-/

namespace SuccessorTree
namespace HalesJewett

inductive IndexedSymbol (α : Type u) where
  | const : α → IndexedSymbol α
  | var : Nat → IndexedSymbol α
  deriving Repr

namespace IndexedSymbol

/-- Regard a one-variable line as using the indexed variable `λ_n`. -/
def fromLine (n : Nat) : LineSymbol α → IndexedSymbol α
  | .const a => .const a
  | .parameter => .var n

end IndexedSymbol

/-- Evaluate an indexed variable word using the supplied finite list.
Evaluation stops at the first variable whose index is outside the supplied
list. -/
def evalIndexed (u : List α) : List (IndexedSymbol α) → List α
  | [] => []
  | .const a :: w => a :: evalIndexed u w
  | .var i :: w =>
      match u[i]? with
      | none => []
      | some a => a :: evalIndexed u w

@[simp] theorem evalIndexed_nil (u : List α) :
    evalIndexed u [] = [] := rfl

@[simp] theorem evalIndexed_const (u : List α) (a : α)
    (w : List (IndexedSymbol α)) :
    evalIndexed u (.const a :: w) = a :: evalIndexed u w := rfl

theorem evalIndexed_var_some (u : List α) (i : Nat) (a : α)
    (w : List (IndexedSymbol α)) (h : u[i]? = some a) :
    evalIndexed u (.var i :: w) = a :: evalIndexed u w := by
  simp [evalIndexed, h]

theorem evalIndexed_var_none (u : List α) (i : Nat)
    (w : List (IndexedSymbol α)) (h : u[i]? = none) :
    evalIndexed u (.var i :: w) = [] := by
  simp [evalIndexed, h]

/-- Replace the parameter of a line by the indexed variable `λ_n`. -/
def indexedLine (n : Nat) (L : StarLine α) : List (IndexedSymbol α) :=
  L.word.map (IndexedSymbol.fromLine n)

/-- With exactly `n` supplied letters, an appended `λ_n`-line evaluates
to its star prefix. -/
theorem evalIndexed_indexedLine_star
    (u : List α) (n : Nat) (w : List (LineSymbol α))
    (hu : u.length = n) :
    evalIndexed u (w.map (IndexedSymbol.fromLine n)) = starPrefix w := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | const a =>
          change a :: evalIndexed u
              (xs.map (IndexedSymbol.fromLine n)) =
            a :: starPrefix xs
          exact congrArg (List.cons a) ih
      | parameter =>
          have hnone : u[n]? = none := by
            rw [List.getElem?_eq_none_iff]
            omega
          simp [IndexedSymbol.fromLine, evalIndexed, hnone, starPrefix]

/-- With one additional supplied letter, the indexed line evaluates exactly
as the ordinary starred line at that letter. -/
theorem evalIndexed_indexedLine_eval
    (u : List α) (n : Nat) (a : α) (w : List (LineSymbol α))
    (hu : u.length = n) :
    evalIndexed (u ++ [a]) (w.map (IndexedSymbol.fromLine n)) =
      evalWord a w := by
  have hget : (u ++ [a])[n]? = some a := by
    rw [List.getElem?_append_right]
    · simp [hu]
    · omega
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | const b =>
          change b :: evalIndexed (u ++ [a])
              (xs.map (IndexedSymbol.fromLine n)) =
            b :: evalWord a xs
          exact congrArg (List.cons b) ih
      | parameter =>
          change
            evalIndexed (u ++ [a])
                (.var n :: xs.map (IndexedSymbol.fromLine n)) =
              a :: evalWord a xs
          rw [evalIndexed_var_some _ _ _ _ hget]
          exact congrArg (List.cons a) ih

@[simp] theorem evalIndexed_indexedLine_star'
    (u : List α) (n : Nat) (L : StarLine α)
    (hu : u.length = n) :
    evalIndexed u (indexedLine n L) = L.star := by
  exact evalIndexed_indexedLine_star u n L.word hu

@[simp] theorem evalIndexed_indexedLine_eval'
    (u : List α) (n : Nat) (a : α) (L : StarLine α)
    (hu : u.length = n) :
    evalIndexed (u ++ [a]) (indexedLine n L) = L.eval a := by
  exact evalIndexed_indexedLine_eval u n a L.word hu

end HalesJewett
end SuccessorTree
