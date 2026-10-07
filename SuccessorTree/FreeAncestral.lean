import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

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

/-- Canonical bounded tuple of ancestral parameter levels.

The tuple has a length at most arity; the j-th used parameter stores its
ancestor level below the current source level n. -/
structure ParamTuple (arity n : Nat) where
  len : Fin (arity + 1)
  value : Fin len.val → Fin n

def paramTupleEquiv (arity n : Nat) :
    ParamTuple arity n ≃
      Sigma (fun len : Fin (arity + 1) => Fin len.val → Fin n) where
  toFun p := ⟨p.len, p.value⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro p
    cases p
    rfl
  right_inv := by
    intro p
    rcases p with ⟨len, value⟩
    rfl

noncomputable instance instFintypeParamTuple (arity n : Nat) :
    Fintype (ParamTuple arity n) :=
  Fintype.ofEquiv
    (Sigma (fun len : Fin (arity + 1) => Fin len.val → Fin n))
    (paramTupleEquiv arity n).symm

/-- One intrinsic transition code at source level n.

The external successor API supplies the actual parameter nodes.  Internally we
remember only the ordered tuple of their ancestor levels; this is enough because
a rooted history has a unique ancestor on every lower level. -/
structure Code (Label : Type u) (arity n : Nat) where
  label : Label
  params : ParamTuple arity n

def codeEquiv (Label : Type u) (arity n : Nat) :
    Code Label arity n ≃ Label × ParamTuple arity n where
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

noncomputable instance instFintypeCode
    [Fintype Label] (arity n : Nat) :
    Fintype (Code Label arity n) :=
  Fintype.ofEquiv
    (Label × ParamTuple arity n)
    (codeEquiv Label arity n).symm

/-- Histories indexed by their level. -/
inductive History (Label : Type u) (arity : Nat) : Nat → Type u
  | root : History Label arity 0
  | step {n : Nat} :
      History Label arity n →
      Code Label arity n →
      History Label arity (n + 1)

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
noncomputable def historyFintype [Fintype Label] :
    (n : Nat) → Fintype (History Label arity n)
  | 0 =>
      Fintype.ofEquiv Unit
        { toFun := fun _ => History.root
          invFun := fun _ => ()
          left_inv := by
            intro u
            cases u
            rfl
          right_inv := by
            intro h
            exact history_zero_unique h }
  | n + 1 => by
      letI : Fintype (History Label arity n) := historyFintype n
      letI : Fintype (Code Label arity n) := inferInstance
      exact Fintype.ofEquiv
        (History Label arity n × Code Label arity n)
        (historySuccEquiv n).symm

noncomputable instance instFintypeHistory [Fintype Label] (n : Nat) :
    Fintype (History Label arity n) :=
  historyFintype n

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

theorem node_level_finite [Fintype Label] (n : Nat) :
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
  letI : Fintype {x : Node Label arity // x.level = n} :=
    Fintype.ofEquiv (History Label arity n) e.symm
  exact Set.toFinite _

end FreeAncestral
end SuccessorTree
