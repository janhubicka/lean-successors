import Mathlib.Data.Finite.Basic
import Mathlib.Data.Fin.Basic

/-! # Free ancestral history syntax

This is a small reusable syntax for the free-history tree used by the girth
successor-tree application. Intrinsic successor parameters are ancestral:
a transition remembers only the levels of a bounded tuple of earlier
occurrences on the same history spine. Intersections with unrelated branches
are deliberately not part of this syntax.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

/-- One intrinsic transition code at source level n.

A parameter value some i means that the slot points to the unique ancestor on
level i < n; none means that parameter slot is unused. -/
structure Code (Label : Type u) (arity n : Nat) where
  label : Label
  params : Fin arity → Option (Fin n)
deriving DecidableEq

def codeEquiv (Label : Type u) (arity n : Nat) :
    Code Label arity n ≃
      Label × (Fin arity → Option (Fin n)) where
  toFun c := ⟨c.label, c.params⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv := by
    intro c
    cases c
    rfl
  right_inv := by
    intro x
    rcases x with ⟨l, p⟩
    rfl

noncomputable instance instFiniteCode
    [Finite Label] (arity n : Nat) :
    Finite (Code Label arity n) :=
  Finite.of_injective
    (codeEquiv Label arity n).toFun
    (codeEquiv Label arity n).injective

/-- Histories indexed by their level. -/
inductive History (Label : Type u) (arity : Nat) : Nat → Type u
  | root : History Label arity 0
  | step {n : Nat} :
      History Label arity n →
      Code Label arity n →
      History Label arity (n + 1)
deriving DecidableEq

variable {Label : Type u} {arity : Nat}

/-- Level zero contains exactly the root history. -/
theorem history_zero_unique (h : History Label arity 0) :
    h = History.root := by
  cases h
  rfl

/-- A positive-level history is uniquely its predecessor together with its
last intrinsic transition code. -/
def historySuccEquiv (n : Nat) :
    History Label arity (n + 1) ≃
      History Label arity n × Code Label arity n where
  toFun := by
    intro h
    cases h with
    | step p c => exact ⟨p, c⟩
  invFun := fun pc => History.step pc.1 pc.2
  left_inv := by
    intro h
    cases h
    rfl
  right_inv := by
    intro pc
    rcases pc with ⟨p, c⟩
    rfl

/-- Every fixed history level is finite when the intrinsic label alphabet is
finite. -/
noncomputable def historyFinite [Finite Label] :
    (n : Nat) → Finite (History Label arity n)
  | 0 =>
      Finite.of_injective
        (fun _ : History Label arity 0 => PUnit.unit)
        (by
          intro x y hxy
          simpa [history_zero_unique x, history_zero_unique y])
  | n + 1 => by
      letI : Finite (History Label arity n) := historyFinite n
      letI : Finite (Code Label arity n) := inferInstance
      exact Finite.of_injective
        (historySuccEquiv n).toFun
        (historySuccEquiv n).injective

noncomputable instance instFiniteHistory [Finite Label] (n : Nat) :
    Finite (History Label arity n) :=
  historyFinite n

/-- Forget the last transition of a positive-level history. -/
def parent {n : Nat} :
    History Label arity (n + 1) → History Label arity n :=
  fun h => (historySuccEquiv n h).1

/-- Read the last intrinsic transition code. -/
def lastCode {n : Nat} :
    History Label arity (n + 1) → Code Label arity n :=
  fun h => (historySuccEquiv n h).2

@[simp] theorem parent_step {n : Nat}
    (h : History Label arity n) (c : Code Label arity n) :
    parent (History.step h c) = h := rfl

@[simp] theorem lastCode_step {n : Nat}
    (h : History Label arity n) (c : Code Label arity n) :
    lastCode (History.step h c) = c := rfl

/-- Total history nodes, carrying their level in the first coordinate. -/
abbrev Node (Label : Type u) (arity : Nat) :=
  Sigma (History Label arity)

/-- The level of a total history node. -/
def Node.level (x : Node Label arity) : Nat := x.1

theorem node_level_finite [Finite Label] (n : Nat) :
    Set.Finite {x : Node Label arity | x.level = n} := by
  classical
  let e :
      {x : Node Label arity // x.level = n} ≃
        History Label arity n :=
    { toFun := by
        intro x
        rcases x with ⟨⟨m, h⟩, hm⟩
        simp only [Node.level] at hm
        subst m
        exact h
      invFun := fun h => ⟨⟨n, h⟩, rfl⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨m, h⟩, hm⟩
        simp only [Node.level] at hm
        subst m
        rfl
      right_inv := by
        intro h
        rfl }
  haveI : Finite {x : Node Label arity // x.level = n} :=
    Finite.of_injective e.toFun e.injective
  exact Set.toFinite _

end FreeAncestral
end SuccessorTree
