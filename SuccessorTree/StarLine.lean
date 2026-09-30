import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
# Starred combinatorial lines

This file isolates the combinatorial object used in the proof of the
one-dimensional pigeonhole lemma in the successor-tree paper.

A `StarLine α` is a finite word over constants from `α` and one distinguished
parameter symbol, required to occur at least once.  Evaluating the parameter at
`a : α` gives an ordinary word.  The `star` evaluation truncates immediately
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

end LineSymbol

/-- The prefix before the first parameter.  Constants after the first parameter
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
          exact ⟨evalWord a (LineSymbol.parameter :: xs), by
            simp [starPrefix]⟩
      | const b =>
          rcases ih with ⟨t, ht⟩
          refine ⟨t, ?_⟩
          simp [starPrefix, evalWord, LineSymbol.eval, ht]

/-- In particular, `L(*)` is a prefix of every `L(a)`. -/
theorem StarLine.star_isPrefix_eval (L : StarLine α) (a : α) :
    L.star <+: L.eval a := by
  exact starPrefix_isPrefix_evalWord L.word a

/-- Turn a constant word into line symbols. -/
def constants (s : List α) : List (LineSymbol α) :=
  s.map LineSymbol.const

@[simp] theorem evalWord_constants (s : List α) (a : α) :
    evalWord a (constants s) = s := by
  simp [evalWord, constants, Function.comp_def, LineSymbol.eval]

@[simp] theorem starPrefix_constants_append (s : List α) (w : List (LineSymbol α)) :
    starPrefix (constants s ++ w) = s ++ starPrefix w := by
  change starPrefix (s.map LineSymbol.const ++ w) = s ++ starPrefix w
  induction s with
  | nil => rfl
  | cons b s ih =>
      simp only [List.map_cons, List.cons_append, starPrefix]
      rw [ih]

@[simp] theorem evalWord_constants_append (s : List α) (w : List (LineSymbol α)) (a : α) :
    evalWord a (constants s ++ w) = s ++ evalWord a w := by
  simp [evalWord, constants, Function.comp_def, LineSymbol.eval]

/-- Prepend a fixed constant support word to a starred line. -/
def StarLine.prepend (s : List α) (L : StarLine α) : StarLine α where
  word := constants s ++ L.word
  hasParameter := by
    simp only [List.mem_append]
    exact Or.inr L.hasParameter

@[simp] theorem StarLine.eval_prepend (s : List α) (L : StarLine α) (a : α) :
    (L.prepend s).eval a = s ++ L.eval a := by
  simp [StarLine.prepend, StarLine.eval]

@[simp] theorem StarLine.star_prepend (s : List α) (L : StarLine α) :
    (L.prepend s).star = s ++ L.star := by
  simp [StarLine.prepend, StarLine.star]

end SuccessorTree
