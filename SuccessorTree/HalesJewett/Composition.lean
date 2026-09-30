import SuccessorTree.HalesJewett.VariableWord
import SuccessorTree.HalesJewett.Forcing
import Mathlib.Tactic

/-!
# Composition of variable-word subspaces

This file makes the substitution algebra used by the combinatorial-forcing
proof concrete.  The representation in `VariableWord.lean` stores an
infinite variable word as a constant head followed by left-variable blocks.

The main theorem is `compose_eval`:

`(W.compose U).eval v = W.eval (U.eval v)`.

It is the exact associativity identity written in the paper as
`W(U(v)) = W(U)(v)`.  Consequently the concrete subspaces instantiate the
abstract `SubspaceAction` used by the largeness lemmas.
-/

namespace SuccessorTree
namespace HalesJewett

namespace Subspace

/-- Substitute one raw symbol of an inner subspace into the corresponding
variable block of `W`. -/
def substSymbolAt (W : Subspace α) (i : Nat) :
    LineSymbol α → List (LineSymbol α)
  | .const a => constants ((W.blocks i).eval a)
  | .parameter => (W.blocks i).word

/-- Substitute a finite raw-symbol segment, consuming successive variable
blocks of `W`. -/
def substSymbolsFrom (W : Subspace α) : Nat → List (LineSymbol α) →
    List (LineSymbol α)
  | _, [] => []
  | i, x :: xs => W.substSymbolAt i x ++ W.substSymbolsFrom (i + 1) xs

@[simp] theorem evalWord_append (a : α)
    (u v : List (LineSymbol α)) :
    evalWord a (u ++ v) = evalWord a u ++ evalWord a v := by
  simp [evalWord]

@[simp] theorem evalWord_substSymbolAt
    (W : Subspace α) (i : Nat) (x : LineSymbol α) (a : α) :
    evalWord a (W.substSymbolAt i x) =
      (W.blocks i).eval (LineSymbol.eval a x) := by
  cases x with
  | const b =>
      simp [substSymbolAt]
  | parameter =>
      simp [substSymbolAt, LeftVariableWord.word, LeftVariableWord.eval,
        evalWord]

/-- Evaluating a substituted raw segment is the same as first evaluating the
inner symbols and then feeding the resulting constant word through `W`. -/
theorem evalWord_substSymbolsFrom
    (W : Subspace α) (i : Nat) (xs : List (LineSymbol α)) (a : α) :
    evalWord a (W.substSymbolsFrom i xs) =
      W.evalFrom i (evalWord a xs) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
      change
        evalWord a (W.substSymbolAt i x ++
          W.substSymbolsFrom (i + 1) xs) =
        (W.blocks i).eval (LineSymbol.eval a x) ++
          W.evalFrom (i + 1) (evalWord a xs)
      rw [evalWord_append, evalWord_substSymbolAt, ih (i + 1)]

/-- Raw position at which the `k`th variable block of `U` starts. -/
def blockStart (U : Subspace α) : Nat → Nat
  | 0 => U.head.length
  | k + 1 => U.blockStart k + 1 + (U.blocks k).tail.length

@[simp] theorem LeftVariableWord.length_eval
    (B : LeftVariableWord α) (a : α) :
    (B.eval a).length = 1 + B.tail.length := by
  simp [LeftVariableWord.eval, evalWord, Nat.add_comm]

/-- Moving to the next inner block consumes exactly the evaluated length of
the current block. -/
theorem blockStart_succ (U : Subspace α) (k : Nat) (a : α) :
    U.blockStart (k + 1) =
      U.blockStart k + ((U.blocks k).eval a).length := by
  simp [blockStart, LeftVariableWord.length_eval, Nat.add_assoc]

/-- The `k`th block of the composite.  The first raw symbol of every inner
block is its variable; substituting it produces a block of `W` whose first
symbol is again the current variable, so dropping that mandatory first symbol
leaves the tail displayed below. -/
def composeBlock (W U : Subspace α) (k : Nat) : LeftVariableWord α :=
  let i := U.blockStart k
  ⟨(W.blocks i).tail ++
    W.substSymbolsFrom (i + 1) (U.blocks k).tail⟩

/-- Evaluation of one composite block. -/
theorem composeBlock_eval (W U : Subspace α) (k : Nat) (a : α) :
    (composeBlock W U k).eval a =
      W.evalFrom (U.blockStart k) ((U.blocks k).eval a) := by
  let i := U.blockStart k
  change
    a :: evalWord a
      ((W.blocks i).tail ++
        W.substSymbolsFrom (i + 1) (U.blocks k).tail) =
      (W.blocks i).eval a ++
        W.evalFrom (i + 1) (evalWord a (U.blocks k).tail)
  rw [evalWord_append, evalWord_substSymbolsFrom]
  simp [LeftVariableWord.eval]

/-- Evaluation from an index distributes over concatenation, with the second
piece starting after the number of letters consumed by the first. -/
theorem evalFrom_append (W : Subspace α) (i : Nat) (u v : List α) :
    W.evalFrom i (u ++ v) =
      W.evalFrom i u ++ W.evalFrom (i + u.length) v := by
  induction u generalizing i with
  | nil =>
      simp [evalFrom]
  | cons a u ih =>
      simp only [List.cons_append, evalFrom, List.length_cons]
      rw [ih (i + 1)]
      have hidx : (i + 1) + u.length = i + (u.length + 1) := by omega
      rw [hidx]
      simp [List.append_assoc]

/-- Composition of two subspaces, i.e. substitution of the inner infinite
variable word into the outer one. -/
def compose (W U : Subspace α) : Subspace α where
  head := W.eval U.head
  blocks := fun k => composeBlock W U k

/-- The core blockwise composition identity. -/
theorem compose_evalFrom (W U : Subspace α) (k : Nat) (v : List α) :
    (compose W U).evalFrom k v =
      W.evalFrom (U.blockStart k) (U.evalFrom k v) := by
  induction v generalizing k with
  | nil => rfl
  | cons a v ih =>
      change
        (composeBlock W U k).eval a ++
            (compose W U).evalFrom (k + 1) v =
          W.evalFrom (U.blockStart k)
            ((U.blocks k).eval a ++ U.evalFrom (k + 1) v)
      rw [composeBlock_eval, ih (k + 1), evalFrom_append,
        blockStart_succ U k a]

/-- Associativity of finite evaluation with subspace substitution:
`W(U(v)) = (W(U))(v)`. -/
theorem compose_eval (W U : Subspace α) (v : List α) :
    (compose W U).eval v = W.eval (U.eval v) := by
  change
    W.eval U.head ++ (compose W U).evalFrom 0 v =
      W.eval (U.head ++ U.evalFrom 0 v)
  rw [compose_evalFrom]
  simp only [eval, evalFrom_append, blockStart]
  simp [List.append_assoc]

/-- Inside the initial identity part of a shift, block starts are unchanged. -/
theorem shift_blockStart_eq
    (U : Subspace α) (n i : Nat) (h : i < n) :
    (shift U n).blockStart i = i := by
  induction i with
  | zero =>
      rw [blockStart, shift_head_of_pos U h]
      rfl
  | succ i ih =>
      have hi : i < n := lt_trans (Nat.lt_succ_self i) h
      rw [blockStart, ih hi]
      have hb := shift_blocks_eq_identity_of_succ_lt U n i h
      rw [hb]
      simp

/-- Positive shifted composition preserves the outer constant head literally. -/
theorem compose_shift_head_eq
    (W U : Subspace α) (n : Nat) (h : 0 < n) :
    (compose W (shift U n)).head = W.head := by
  change W.eval (shift U n).head = W.head
  rw [shift_head_of_pos U h]
  exact W.eval_nil

/-- Blocks strictly below the last identity coordinate are literally preserved
by shifted composition. -/
theorem compose_shift_blocks_eq
    (W U : Subspace α) (n i : Nat) (h : i + 1 < n) :
    (compose W (shift U n)).blocks i = W.blocks i := by
  change composeBlock W (shift U n) i = W.blocks i
  unfold composeBlock
  rw [shift_blockStart_eq U n i (lt_of_succ_lt h),
    shift_blocks_eq_identity_of_succ_lt U n i h]
  cases hB : W.blocks i with
  | mk tail =>
      simp [hB, substSymbolsFrom]

/-- Composing with a shift does not change evaluations strictly below the
shift level.  This is the corrected stabilization property used in forcing
Lemma 2. -/
theorem compose_shift_eval_of_length_lt
    (W U : Subspace α) (n : Nat) (u : List α)
    (h : u.length < n) :
    (compose W (shift U n)).eval u = W.eval u := by
  rw [compose_eval, shift_eval_of_length_lt U n u h]

/-- General prefix/tail Shift identity after outer composition. -/
theorem compose_shift_eval_append_of_length_le
    (W U : Subspace α) (n : Nat) (u v : List α)
    (h : u.length ≤ n) :
    (compose W (shift U n)).eval (u ++ v) =
      W.eval (u ++ (shift U (n - u.length)).eval v) := by
  rw [compose_eval, shift_eval_append_of_length_le U n u v h]

/-- The paper's Shift observation:
if `u` has length `n`, then
`W(Shift(U,n))(u⌢v) = W(u⌢U(v))`. -/
theorem compose_shift_eval_append
    (W U : Subspace α) (n : Nat) (u v : List α)
    (hu : u.length = n) :
    (compose W (shift U n)).eval (u ++ v) =
      W.eval (u ++ U.eval v) := by
  rw [compose_eval, shift_eval_append U n u v hu]

end Subspace

/-- Concrete substitution action of infinite variable words on finite words. -/
def subspaceAction (α : Type u) :
    SubspaceAction (List α) (Subspace α) where
  act := Subspace.eval
  id := Subspace.identity
  comp := Subspace.compose
  act_id := Subspace.identity_eval
  act_comp := Subspace.compose_eval

end HalesJewett
end SuccessorTree
