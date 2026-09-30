import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
# Starred combinatorial lines

This file isolates the combinatorial object used in the proof of the
one-dimensional pigeonhole lemma in the successor-tree paper.

A `StarLine α` is a finite word over constants from `α` and one distinguished
parameter symbol, required to occur at least once. Evaluating the parameter at
`a : α` gives an ordinary word. The `star` evaluation truncates immediately
before the first parameter, exactly as in the paper's `L(*)` notation.
-/

namespace SuccessorTree

inductive LineSymbol (α : Type u) where
  | const : α → LineSymbol α
  | parameter : LineSymbol α
  deriving Repr

namespace LineSymbol

/-- Evaluate a line symbol by replacing the parameter with `a`. -/
def eval (a : α) : LineSymbol α → α
  | const b => b
  | parameter => a

@[simp] theorem eval_const (a b : α) : eval a (.const b) = b := rfl
@[simp] theorem eval_parameter (a : α) : eval a (.parameter) = a := rfl

end LineSymbol

/-- The prefix before the first parameter. Constants after the first parameter
are intentionally discarded. -/
def starPrefix : List (LineSymbol α) → List α
  | [] => []
  | LineSymbol.parameter :: _ => []
  | LineSymbol.const a :: w => a :: starPrefix w

/-- Evaluate every parameter occurrence of a line word at `a`. -/
def evalWord (a : α) (w : List (LineSymbol α)) : List α :=
  w.map (LineSymbol.eval a)

/-- A finite parameter word with at least one occurrence of the parameter. -/
structure StarLine (α : Type u) where
  word : List (LineSymbol α)
  hasParameter : LineSymbol.parameter ∈ word

namespace StarLine

/-- Ordinary evaluation `L(a)`. -/
def eval (L : StarLine α) (a : α) : List α :=
  evalWord a L.word

/-- Star evaluation `L(*)`: truncate before the first parameter. -/
def star (L : StarLine α) : List α :=
  starPrefix L.word

@[simp] theorem eval_mk (w : List (LineSymbol α)) (h) (a : α) :
    (StarLine.mk w h).eval a = evalWord a w := rfl

@[simp] theorem star_mk (w : List (LineSymbol α)) (h) :
    (StarLine.mk w h).star = starPrefix w := rfl

end StarLine

/-- The starred prefix is a prefix of every ordinary evaluation. -/
theorem starPrefix_isPrefix_evalWord (w : List (LineSymbol α)) (a : α) :
    starPrefix w <+: evalWord a w := by
  induction w with
  | nil =>
      exact ⟨[], rfl⟩
  | cons x xs ih =>
      cases x with
      | parameter =>
          refine ⟨a :: evalWord a xs, ?_⟩
          rfl
      | const b =>
          rcases ih with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          simpa [starPrefix, evalWord] using congrArg (List.cons b) ht

/-- In particular, `L(*)` is a prefix of every `L(a)`. -/
theorem StarLine.star_isPrefix_eval (L : StarLine α) (a : α) :
    L.star <+: L.eval a := by
  exact starPrefix_isPrefix_evalWord L.word a

/-- The raw tail strictly after the first parameter occurrence. -/
def afterFirstParameter : List (LineSymbol α) → List (LineSymbol α)
  | [] => []
  | LineSymbol.parameter :: w => w
  | LineSymbol.const _ :: w => afterFirstParameter w

/-- Turn a constant word into line symbols. -/
def constants (s : List α) : List (LineSymbol α) :=
  s.map LineSymbol.const

@[simp] theorem constants_nil : constants ([] : List α) = [] := rfl

@[simp] theorem constants_cons (a : α) (s : List α) :
    constants (a :: s) = LineSymbol.const a :: constants s := rfl

@[simp] theorem evalWord_constants (s : List α) (a : α) :
    evalWord a (constants s) = s := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      change b :: evalWord a (constants s) = b :: s
      exact congrArg (List.cons b) ih

@[simp] theorem starPrefix_constants_append (s : List α) (w : List (LineSymbol α)) :
    starPrefix (constants s ++ w) = s ++ starPrefix w := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      change b :: starPrefix (constants s ++ w) = b :: (s ++ starPrefix w)
      exact congrArg (List.cons b) ih

@[simp] theorem evalWord_constants_append (s : List α) (w : List (LineSymbol α)) (a : α) :
    evalWord a (constants s ++ w) = s ++ evalWord a w := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      change b :: evalWord a (constants s ++ w) = b :: (s ++ evalWord a w)
      exact congrArg (List.cons b) ih

/-- Raw decomposition at the first parameter. -/
theorem rawWord_eq_constants_star_parameter_tail
    (w : List (LineSymbol α))
    (h : LineSymbol.parameter ∈ w) :
    w =
      constants (starPrefix w) ++
        (LineSymbol.parameter :: afterFirstParameter w) := by
  induction w with
  | nil =>
      simp at h
  | cons x xs ih =>
      cases x with
      | parameter =>
          rfl
      | const a =>
          have htail : LineSymbol.parameter ∈ xs := by
            simpa using h
          simp only [starPrefix, afterFirstParameter, constants_cons,
            List.cons_append]
          exact congrArg (List.cons (LineSymbol.const a)) (ih htail)

/-- A starred line decomposes into its constant star prefix, its first
parameter, and the remaining raw tail. -/
theorem StarLine.word_eq_constants_star_parameter_tail (L : StarLine α) :
    L.word =
      constants L.star ++
        (LineSymbol.parameter :: afterFirstParameter L.word) := by
  exact rawWord_eq_constants_star_parameter_tail L.word L.hasParameter

/-- Ordinary evaluation of a starred line has the corresponding decomposition. -/
theorem StarLine.eval_eq_star_parameter_tail (L : StarLine α) (a : α) :
    L.eval a =
      L.star ++ (a :: evalWord a (afterFirstParameter L.word)) := by
  calc
    L.eval a = evalWord a L.word := rfl
    _ = evalWord a
        (constants L.star ++
          (LineSymbol.parameter :: afterFirstParameter L.word)) := by
      exact congrArg (evalWord a) L.word_eq_constants_star_parameter_tail
    _ = L.star ++
        (a :: evalWord a (afterFirstParameter L.word)) := by
      rw [evalWord_constants_append]
      rfl

@[simp] theorem StarLine.length_eval (L : StarLine α) (a : α) :
    (L.eval a).length = L.word.length := by
  simp [StarLine.eval, evalWord]

theorem StarLine.length_star_lt_word_length (L : StarLine α) :
    L.star.length < L.word.length := by
  have hlen := congrArg List.length L.word_eq_constants_star_parameter_tail
  simp [constants] at hlen
  omega

theorem StarLine.length_star_le_word_length (L : StarLine α) :
    L.star.length ≤ L.word.length :=
  Nat.le_of_lt L.length_star_lt_word_length

/-- Prepend a fixed constant support word to a starred line. -/
def StarLine.prepend (s : List α) (L : StarLine α) : StarLine α where
  word := constants s ++ L.word
  hasParameter := by
    simp only [List.mem_append]
    exact Or.inr L.hasParameter

@[simp] theorem StarLine.eval_prepend (s : List α) (L : StarLine α) (a : α) :
    (L.prepend s).eval a = s ++ L.eval a := by
  exact evalWord_constants_append s L.word a

@[simp] theorem StarLine.star_prepend (s : List α) (L : StarLine α) :
    (L.prepend s).star = s ++ L.star := by
  exact starPrefix_constants_append s L.word

end SuccessorTree
