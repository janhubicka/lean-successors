import SuccessorTree.StarLine

/-!
# Variable words and subspaces

A convenient normal form for the Hubička--Smolík proof is a constant prefix
followed by infinitely many *left-variable blocks*.  Block `i` begins with
`λ_i`, may contain more copies of `λ_i` and constants, and ends immediately
before the first occurrence of `λ_(i+1)`.  Thus the ordering condition on
variables is built into the datatype.

This file develops the finite evaluation operation and the paper's `Shift`.
The key theorem `shift_eval_append` is the basic prefix/tail calculation used
throughout the combinatorial-forcing proof.
-/

namespace SuccessorTree
namespace HalesJewett

/-- A block beginning with its distinguished variable.  We store only the
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
  prefix : List α
  block : Nat → LeftVariableWord α

namespace Subspace

/-- Evaluate successive blocks, starting at block `i`. -/
def evalFrom (W : Subspace α) (i : Nat) : List α → List α
  | [] => []
  | a :: u => (W.block i).eval a ++ W.evalFrom (i + 1) u

/-- Substitute a finite constant word and truncate before the next variable. -/
def eval (W : Subspace α) (u : List α) : List α :=
  W.prefix ++ W.evalFrom 0 u

@[simp] theorem eval_nil (W : Subspace α) : W.eval [] = W.prefix := by
  simp [eval, evalFrom]

@[simp] theorem evalFrom_singletonBlock (i : Nat) (u : List α) :
    ({ prefix := []; block := fun _ => ⟨[]⟩ } : Subspace α).evalFrom i u = u := by
  induction u generalizing i with
  | nil => simp [evalFrom]
  | cons a u ih => simp [evalFrom, LeftVariableWord.eval, ih]

/-- The identity subspace `λ₀ λ₁ λ₂ ...`. -/
def identity : Subspace α where
  prefix := []
  block := fun _ => ⟨[]⟩

@[simp] theorem identity_eval (u : List α) : (identity : Subspace α).eval u = u := by
  simp [eval, identity, evalFrom_singletonBlock]

/-- Prepend one identity variable and shift all variables of `W` by one.
In paper notation this is `λ₀ ⌢ W⁺`. -/
def prependIdentity (W : Subspace α) : Subspace α where
  prefix := []
  block
    | 0 => ⟨constants W.prefix⟩
    | i + 1 => W.block i

@[simp] theorem prependIdentity_evalFrom_succ
    (W : Subspace α) (i : Nat) (u : List α) :
    (prependIdentity W).evalFrom (i + 1) u = W.evalFrom i u := by
  induction u generalizing i with
  | nil => simp [evalFrom]
  | cons a u ih =>
      simp [evalFrom, prependIdentity, ih, Nat.add_assoc]

@[simp] theorem prependIdentity_eval_cons
    (W : Subspace α) (a : α) (u : List α) :
    (prependIdentity W).eval (a :: u) = a :: W.eval u := by
  simp [eval, evalFrom, prependIdentity, LeftVariableWord.eval,
    evalWord_constants, prependIdentity_evalFrom_succ, List.append_assoc]

/-- `Shift(W,n)` from the paper: prepend `n` identity variables and rename the
variables of `W` by adding `n`. -/
def shift (W : Subspace α) : Nat → Subspace α
  | 0 => W
  | n + 1 => prependIdentity (shift W n)

@[simp] theorem shift_zero (W : Subspace α) : shift W 0 = W := rfl

@[simp] theorem shift_succ (W : Subspace α) (n : Nat) :
    shift W (n + 1) = prependIdentity (shift W n) := rfl

/-- Fundamental shift identity.  If `u` has length `n`, then the first `n`
coordinates of `Shift(W,n)` are the identity coordinates and the tail acts as
`W` on `v`. -/
theorem shift_eval_append
    (W : Subspace α) (n : Nat) (u v : List α) (hu : u.length = n) :
    (shift W n).eval (u ++ v) = u ++ W.eval v := by
  induction n generalizing u with
  | zero =>
      cases u with
      | nil => simp [shift]
      | cons a u => simp at hu
  | succ n ih =>
      cases u with
      | nil => simp at hu
      | cons a u =>
          have hut : u.length = n := by simpa using Nat.succ.inj hu
          simp [shift, prependIdentity_eval_cons, ih u v hut]

/-- The first coordinate of a subspace as a starred combinatorial line. -/
def firstLine (W : Subspace α) : StarLine α where
  word := constants W.prefix ++ (LineSymbol.parameter :: (W.block 0).tail)
  hasParameter := by simp

@[simp] theorem firstLine_star (W : Subspace α) : W.firstLine.star = W.prefix := by
  simp [firstLine, StarLine.star, starPrefix]

@[simp] theorem firstLine_eval (W : Subspace α) (a : α) :
    W.firstLine.eval a = W.eval [a] := by
  simp [firstLine, StarLine.eval, eval, evalFrom, LeftVariableWord.eval,
    evalWord, List.append_assoc]

end Subspace

end HalesJewett
end SuccessorTree
