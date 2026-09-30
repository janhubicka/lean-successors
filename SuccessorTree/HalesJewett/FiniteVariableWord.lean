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


/-- Extract the variable indices occurring in an indexed word. -/
def variableIndices : List (IndexedSymbol α) → List Nat
  | [] => []
  | .const _ :: w => variableIndices w
  | .var i :: w => i :: variableIndices w

@[simp] theorem variableIndices_nil :
    variableIndices ([] : List (IndexedSymbol α)) = [] := rfl

@[simp] theorem variableIndices_const (a : α)
    (w : List (IndexedSymbol α)) :
    variableIndices (.const a :: w) = variableIndices w := rfl

@[simp] theorem variableIndices_var (i : Nat)
    (w : List (IndexedSymbol α)) :
    variableIndices (.var i :: w) = i :: variableIndices w := rfl

@[simp] theorem variableIndices_append
    (u v : List (IndexedSymbol α)) :
    variableIndices (u ++ v) = variableIndices u ++ variableIndices v := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> simp [ih]

/-- Number of parameter occurrences in a one-variable raw word. -/
def parameterCount : List (LineSymbol α) → Nat
  | [] => 0
  | .const _ :: w => parameterCount w
  | .parameter :: w => parameterCount w + 1

theorem parameterCount_pos_of_mem
    (w : List (LineSymbol α))
    (h : LineSymbol.parameter ∈ w) :
    0 < parameterCount w := by
  induction w with
  | nil => simp at h
  | cons x xs ih =>
      cases x with
      | const a =>
          simp only [List.mem_cons] at h
          rcases h with h | h
          · cases h
          · exact ih h
      | parameter =>
          simp [parameterCount]

/-- An indexed line contributes only copies of its new variable. -/
theorem variableIndices_indexedLine
    (n : Nat) (L : StarLine α) :
    variableIndices (indexedLine n L) =
      List.replicate (parameterCount L.word) n := by
  unfold indexedLine
  induction L.word with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | const a =>
          simpa [IndexedSymbol.fromLine, variableIndices, parameterCount] using ih
      | parameter =>
          simp [IndexedSymbol.fromLine, variableIndices, parameterCount, ih,
            List.replicate_succ]

/-- The new variable really occurs in an indexed starred line. -/
theorem newVariable_mem_indexedLine
    (n : Nat) (L : StarLine α) :
    n ∈ variableIndices (indexedLine n L) := by
  rw [variableIndices_indexedLine]
  have hp : 0 < parameterCount L.word :=
    parameterCount_pos_of_mem L.word L.hasParameter
  simpa using hp

/-- All variables in an indexed line have the selected index. -/
theorem eq_newVariable_of_mem_indexedLine
    {n i : Nat} {L : StarLine α}
    (h : i ∈ variableIndices (indexedLine n L)) :
    i = n := by
  rw [variableIndices_indexedLine] at h
  simpa using h

/-- A concrete finite `n`-variable word.

The variable-index list is nondecreasing, every index below `n` occurs, and
no index at least `n` occurs.  This is equivalent to the ordering convention
in the forcing note. -/
structure FiniteVariableWord (α : Type u) (n : Nat) where
  raw : List (IndexedSymbol α)
  ordered : (variableIndices raw).Pairwise (· ≤ ·)
  below : ∀ i ∈ variableIndices raw, i < n
  occurs : ∀ i, i < n → i ∈ variableIndices raw

namespace FiniteVariableWord

/-- Evaluate a finite variable word on a finite list of letters. -/
def eval (U : FiniteVariableWord α n) (u : List α) : List α :=
  evalIndexed u U.raw

/-- Append a starred line as the new variable `λ_n`. -/
def extendByLine (U : FiniteVariableWord α n) (L : StarLine α) :
    FiniteVariableWord α (n + 1) where
  raw := U.raw ++ indexedLine n L
  ordered := by
    rw [variableIndices_append, List.pairwise_append]
    refine ⟨U.ordered, ?_, ?_⟩
    · apply List.pairwise_of_forall_mem_list
      intro i hi j hj
      have hi' := eq_newVariable_of_mem_indexedLine hi
      have hj' := eq_newVariable_of_mem_indexedLine hj
      omega
    · intro i hi j hj
      have hi' := U.below i hi
      have hj' := eq_newVariable_of_mem_indexedLine hj
      omega
  below := by
    intro i hi
    rw [variableIndices_append] at hi
    rcases List.mem_append.mp hi with hi | hi
    · exact Nat.lt.step (U.below i hi)
    · have hi' := eq_newVariable_of_mem_indexedLine hi
      omega
  occurs := by
    intro i hi
    rw [variableIndices_append]
    by_cases hin : i < n
    · exact List.mem_append_left _ (U.occurs i hin)
    · have hieq : i = n := by omega
      subst i
      exact List.mem_append_right _ (newVariable_mem_indexedLine n L)

/-- Every variable of `U` is resolvable by a list of length at least `n`. -/
theorem resolvable_of_length_ge
    (U : FiniteVariableWord α n) (u : List α)
    (h : n ≤ u.length) :
    ∀ i ∈ variableIndices U.raw, i < u.length := by
  intro i hi
  exact lt_of_lt_of_le (U.below i hi) h

end FiniteVariableWord

end HalesJewett
end SuccessorTree
