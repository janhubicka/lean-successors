import SuccessorTree.HalesJewett.Composition
import Mathlib.Tactic

/-!
# Alphabet extension plumbing

This file develops the concrete substitution identities used in the induction
from an alphabet alpha to Option alpha.
-/

namespace SuccessorTree
namespace HalesJewett

def optionWord (u : List α) : List (Option α) :=
  u.map some

def optionSymbol : LineSymbol α → LineSymbol (Option α)
  | .const a => .const (some a)
  | .parameter => .parameter

@[simp] theorem evalWord_optionSymbol
    (a : α) (w : List (LineSymbol α)) :
    evalWord (some a) (w.map optionSymbol) =
      optionWord (evalWord a w) := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | const b =>
          change
            some b :: evalWord (some a) (xs.map optionSymbol) =
              some b :: optionWord (evalWord a xs)
          exact congrArg (List.cons (some b)) ih
      | parameter =>
          change
            some a :: evalWord (some a) (xs.map optionSymbol) =
              some a :: optionWord (evalWord a xs)
          exact congrArg (List.cons (some a)) ih

def LeftVariableWord.optionLift
    (B : LeftVariableWord α) : LeftVariableWord (Option α) :=
  ⟨B.tail.map optionSymbol⟩

@[simp] theorem LeftVariableWord.optionLift_eval
    (B : LeftVariableWord α) (a : α) :
    B.optionLift.eval (some a) = optionWord (B.eval a) := by
  simp [LeftVariableWord.optionLift, LeftVariableWord.eval,
    optionWord, evalWord_optionSymbol]

def Subspace.optionLift (W : Subspace α) : Subspace (Option α) where
  head := optionWord W.head
  blocks := fun i => (W.blocks i).optionLift

@[simp] theorem Subspace.optionLift_evalFrom
    (W : Subspace α) (i : Nat) (u : List α) :
    W.optionLift.evalFrom i (optionWord u) =
      optionWord (W.evalFrom i u) := by
  induction u generalizing i with
  | nil => rfl
  | cons a u ih =>
      change
        (W.blocks i).optionLift.eval (some a) ++
            W.optionLift.evalFrom (i + 1) (optionWord u) =
          optionWord ((W.blocks i).eval a ++ W.evalFrom (i + 1) u)
      rw [LeftVariableWord.optionLift_eval, ih]
      simp [optionWord, List.map_append]

@[simp] theorem Subspace.optionLift_eval
    (W : Subspace α) (u : List α) :
    W.optionLift.eval (optionWord u) = optionWord (W.eval u) := by
  change
    optionWord W.head ++ W.optionLift.evalFrom 0 (optionWord u) =
      optionWord (W.head ++ W.evalFrom 0 u)
  rw [Subspace.optionLift_evalFrom]
  simp [optionWord, List.map_append]

def nestedSubspace : List (Subspace α) → Subspace (Option α)
  | [] => Subspace.identity
  | W :: Ws =>
      W.optionLift.compose ((nestedSubspace Ws).shift 1)

@[simp] theorem nestedSubspace_nil :
    nestedSubspace ([] : List (Subspace α)) =
      (Subspace.identity : Subspace (Option α)) := rfl

theorem nestedSubspace_cons_eval_nil
    (W : Subspace α) (Ws : List (Subspace α)) :
    (nestedSubspace (W :: Ws)).eval [] =
      optionWord (W.eval []) := by
  rw [nestedSubspace, Subspace.compose_eval]
  have hhead :
      ((nestedSubspace Ws).shift 1).eval ([] : List (Option α)) = [] := by
    rw [Subspace.eval_nil, Subspace.shift_head_of_pos]
    omega
  rw [hhead]
  exact W.optionLift_eval []

theorem nestedSubspace_cons_eval_cons
    (W : Subspace α) (Ws : List (Subspace α))
    (x : Option α) (v : List (Option α)) :
    (nestedSubspace (W :: Ws)).eval (x :: v) =
      W.optionLift.eval (x :: (nestedSubspace Ws).eval v) := by
  rw [nestedSubspace, Subspace.compose_eval]
  have hshift :=
    Subspace.shift_eval_append
      (nestedSubspace Ws) 1 [x] v rfl
  simpa using hshift

def IsOptionLifted (v : List (Option α)) : Prop :=
  ∃ u : List α, optionWord u = v

theorem nestedSubspace_eval_optionWord
    (Ws : List (Subspace α)) (u : List α) :
    IsOptionLifted ((nestedSubspace Ws).eval (optionWord u)) := by
  induction Ws generalizing u with
  | nil =>
      exact ⟨u, by simp [nestedSubspace, optionWord]⟩
  | cons W Ws ih =>
      cases u with
      | nil =>
          refine ⟨W.eval [], ?_⟩
          exact (nestedSubspace_cons_eval_nil W Ws).symm
      | cons a u =>
          obtain ⟨t, ht⟩ := ih u
          refine ⟨W.eval (a :: t), ?_⟩
          change
            optionWord (W.eval (a :: t)) =
              (nestedSubspace (W :: Ws)).eval
                (some a :: optionWord u)
          rw [nestedSubspace_cons_eval_cons]
          rw [← ht]
          exact (W.optionLift_eval (a :: t)).symm

/-- If a nonempty nested system starts with W and is fed a nonempty
old-letter word, its output is the lift of W evaluated at some old-letter
word. This is the formal v_a used in the alphabet-increase proof. -/
theorem nestedSubspace_cons_eval_optionWord
    (W : Subspace α) (Ws : List (Subspace α))
    (a : α) (u : List α) :
    ∃ t : List α,
      (nestedSubspace (W :: Ws)).eval (optionWord (a :: u)) =
        optionWord (W.eval t) := by
  obtain ⟨v, hv⟩ := nestedSubspace_eval_optionWord Ws u
  refine ⟨a :: v, ?_⟩
  change
    (nestedSubspace (W :: Ws)).eval
        (some a :: optionWord u) =
      optionWord (W.eval (a :: v))
  rw [nestedSubspace_cons_eval_cons]
  rw [← hv]
  exact W.optionLift_eval (a :: v)

def prefixApply : List (Subspace α) → List (Option α) → List (Option α)
  | [], v => v
  | W :: Ws, v =>
      W.optionLift.eval (none :: prefixApply Ws v)

@[simp] theorem prefixApply_nil (v : List (Option α)) :
    prefixApply ([] : List (Subspace α)) v = v := rfl

theorem prefixApply_append
    (As Bs : List (Subspace α)) (v : List (Option α)) :
    prefixApply (As ++ Bs) v =
      prefixApply As (prefixApply Bs v) := by
  induction As with
  | nil => rfl
  | cons W As ih =>
      simp only [List.cons_append, prefixApply]
      rw [ih]

theorem nestedSubspace_eval_none_prefix
    (As Bs : List (Subspace α)) (v : List (Option α)) :
    (nestedSubspace (As ++ Bs)).eval
        (List.replicate As.length none ++ v) =
      prefixApply As ((nestedSubspace Bs).eval v) := by
  induction As with
  | nil =>
      simp [nestedSubspace, prefixApply]
  | cons W As ih =>
      change
        (nestedSubspace (W :: (As ++ Bs))).eval
            (none :: (List.replicate As.length none ++ v)) =
          W.optionLift.eval
            (none :: prefixApply As ((nestedSubspace Bs).eval v))
      rw [nestedSubspace_cons_eval_cons, ih]

end HalesJewett
end SuccessorTree
