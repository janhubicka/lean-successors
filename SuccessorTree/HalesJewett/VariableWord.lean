import SuccessorTree.StarLine

/-!
# Variable words and subspaces

A convenient normal form for the Hubička--Smolík proof is a constant head
followed by infinitely many *left-variable blocks*. Block `i` begins with
`λ_i`, may contain more copies of `λ_i` and constants, and ends immediately
before the first occurrence of `λ_(i+1)`. Thus the ordering condition on
variables is built into the datatype.

This file develops finite evaluation and the paper's `Shift` operation. The
key theorem `shift_eval_append` is the prefix/tail calculation used throughout
the combinatorial-forcing proof.
-/

namespace SuccessorTree
namespace HalesJewett

/-- A block beginning with its distinguished variable. We store only the
symbols after the mandatory first variable. -/
structure LeftVariableWord (α : Type u) where
  tail : List (LineSymbol α)

namespace LeftVariableWord

/-- The full one-variable block. -/
def word (B : LeftVariableWord α) : List (LineSymbol α) :=
  LineSymbol.parameter :: B.tail

/-- Substitute a letter for the block variable. -/
def eval (B : LeftVariableWord α) (a : α) : List α :=
  a :: evalWord a B.tail

@[simp] theorem eval_mk (tail : List (LineSymbol α)) (a : α) :
    (LeftVariableWord.mk tail).eval a = a :: evalWord a tail := rfl

end LeftVariableWord

/-- An infinite variable word in block normal form. -/
structure Subspace (α : Type u) where
  head : List α
  blocks : Nat → LeftVariableWord α

namespace Subspace

/-- Evaluate successive blocks, starting at block `i`. -/
def evalFrom (W : Subspace α) (i : Nat) : List α → List α
  | [] => []
  | a :: u => (W.blocks i).eval a ++ W.evalFrom (i + 1) u

/-- Substitute a finite constant word and truncate before the next variable. -/
def eval (W : Subspace α) (u : List α) : List α :=
  W.head ++ W.evalFrom 0 u

@[simp] theorem eval_nil (W : Subspace α) : W.eval [] = W.head := by
  simp [eval, evalFrom]

/-- The identity subspace `λ₀ λ₁ λ₂ ...`. -/
def identity : Subspace α where
  head := []
  blocks := fun _ => ⟨[]⟩

@[simp] theorem identity_evalFrom (i : Nat) (u : List α) :
    (identity : Subspace α).evalFrom i u = u := by
  induction u generalizing i with
  | nil => rfl
  | cons a u ih =>
      change a :: (identity : Subspace α).evalFrom (i + 1) u = a :: u
      exact congrArg (List.cons a) (ih (i + 1))

@[simp] theorem identity_eval (u : List α) :
    (identity : Subspace α).eval u = u := by
  change [] ++ (identity : Subspace α).evalFrom 0 u = u
  simp

/-- Prepend one identity variable and shift all variables of `W` by one.
In paper notation this is `λ₀ ⌢ W⁺`. -/
def prependIdentity (W : Subspace α) : Subspace α where
  head := []
  blocks := fun
    | 0 => ⟨constants W.head⟩
    | i + 1 => W.blocks i

@[simp] theorem prependIdentity_evalFrom_succ
    (W : Subspace α) (i : Nat) (u : List α) :
    (prependIdentity W).evalFrom (i + 1) u = W.evalFrom i u := by
  induction u generalizing i with
  | nil => rfl
  | cons a u ih =>
      change
        (W.blocks i).eval a ++
            (prependIdentity W).evalFrom ((i + 1) + 1) u =
          (W.blocks i).eval a ++ W.evalFrom (i + 1) u
      rw [ih (i + 1)]

@[simp] theorem prependIdentity_eval_cons
    (W : Subspace α) (a : α) (u : List α) :
    (prependIdentity W).eval (a :: u) = a :: W.eval u := by
  change
    (a :: evalWord a (constants W.head)) ++
        (prependIdentity W).evalFrom 1 u =
      a :: (W.head ++ W.evalFrom 0 u)
  rw [evalWord_constants, prependIdentity_evalFrom_succ W 0 u]
  rfl

/-- `Shift(W,n)` from the paper: prepend `n` identity variables and rename
the variables of `W` by adding `n`. -/
def shift (W : Subspace α) : Nat → Subspace α
  | 0 => W
  | n + 1 => prependIdentity (shift W n)

@[simp] theorem shift_zero (W : Subspace α) : shift W 0 = W := rfl

@[simp] theorem shift_succ (W : Subspace α) (n : Nat) :
    shift W (n + 1) = prependIdentity (shift W n) := rfl

/-- Fundamental shift identity. If `u` has length `n`, then the first `n`
coordinates of `Shift(W,n)` are the identity coordinates and the tail acts as
`W` on `v`. -/
theorem shift_eval_append
    (W : Subspace α) (n : Nat) (u v : List α) (hu : u.length = n) :
    (shift W n).eval (u ++ v) = u ++ W.eval v := by
  induction n generalizing u with
  | zero =>
      have hu0 : u = [] := List.length_eq_zero_iff.mp hu
      subst u
      simp
  | succ n ih =>
      cases u with
      | nil => simp at hu
      | cons a u =>
          have hut : u.length = n := by
            exact Nat.succ.inj hu
          simp only [List.cons_append, shift_succ, prependIdentity_eval_cons]
          rw [ih u hut]

/-- The first coordinate of a subspace as a starred combinatorial line. -/
def firstLine (W : Subspace α) : StarLine α where
  word := constants W.head ++ (LineSymbol.parameter :: (W.blocks 0).tail)
  hasParameter := by simp

@[simp] theorem firstLine_star (W : Subspace α) : W.firstLine.star = W.head := by
  simp [firstLine, StarLine.star, starPrefix]

@[simp] theorem firstLine_eval (W : Subspace α) (a : α) :
    W.firstLine.eval a = W.eval [a] := by
  change
    evalWord a (constants W.head ++
      (LineSymbol.parameter :: (W.blocks 0).tail)) =
    W.head ++ ((W.blocks 0).eval a ++ [])
  rw [evalWord_constants_append]
  simp [evalWord, LeftVariableWord.eval]

end Subspace

end HalesJewett
end SuccessorTree
