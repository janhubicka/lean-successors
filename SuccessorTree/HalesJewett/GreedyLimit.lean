import SuccessorTree.HalesJewett.Composition
import SuccessorTree.HalesJewett.FiniteVariableWord
import Mathlib.Tactic

/-!
# Greedy extension limits for the forcing proof

A greedy chain of finite variable words is obtained by adjoining starred lines
`L₀,L₁,...`.  This file constructs the corresponding infinite subspace in
the block normal form used by `VariableWord.lean` and proves that its finite
evaluations agree with the appropriate finite stage.

The crucial identity is

`greedyLimit(U₀,L).eval u = extendChain(U₀,L,|u|+1).eval u`.

This is the formal content of the "greedily construct an ω-variable word"
step in forcing Lemma 1.
-/

namespace SuccessorTree
namespace HalesJewett

/-- Concatenate the ordinary evaluations of successive lines, with no final
star prefix. -/
def lineBodyChain (L : Nat → StarLine α) : Nat → List α → List α
  | _, [] => []
  | i, a :: u => (L i).eval a ++ lineBodyChain L (i + 1) u

/-- Concatenate successive line evaluations and finish with the star prefix of
the first line not supplied a letter. -/
def lineChain (L : Nat → StarLine α) : Nat → List α → List α
  | i, [] => (L i).star
  | i, a :: u => (L i).eval a ++ lineChain L (i + 1) u

theorem lineBodyChain_append_last
    (L : Nat → StarLine α) (i : Nat) (u : List α) (a : α) :
    lineBodyChain L i (u ++ [a]) =
      lineBodyChain L i u ++ (L (i + u.length)).eval a := by
  induction u generalizing i with
  | nil =>
      simp [lineBodyChain]
  | cons b u ih =>
      simp only [List.cons_append, lineBodyChain, List.length_cons]
      rw [ih (i + 1)]
      have hidx : (i + 1) + u.length = i + (u.length + 1) := by omega
      rw [hidx]
      simp [List.append_assoc]

theorem lineChain_eq_body_append_star
    (L : Nat → StarLine α) (i : Nat) (u : List α) :
    lineChain L i u =
      lineBodyChain L i u ++ (L (i + u.length)).star := by
  induction u generalizing i with
  | nil =>
      simp [lineChain, lineBodyChain]
  | cons a u ih =>
      simp only [lineChain, lineBodyChain, List.length_cons]
      rw [ih (i + 1)]
      have hidx : (i + 1) + u.length = i + (u.length + 1) := by omega
      rw [hidx]
      simp [List.append_assoc]

/-- Infinite block-normal-form word obtained from a constant initial head and
a sequence of extension lines.

The star prefix of `L₀` is part of the head.  For every `i`, the block
starting at variable `i` consists of the part of `Lᵢ` after its first
parameter followed by the star prefix of `Lᵢ₊₁`.
-/
def limitSubspace (head₀ : List α) (L : Nat → StarLine α) :
    Subspace α where
  head := head₀ ++ (L 0).star
  blocks := fun i =>
    ⟨afterFirstParameter (L i).word ++ constants (L (i + 1)).star⟩

@[simp] theorem limitSubspace_block_eval
    (head₀ : List α) (L : Nat → StarLine α) (i : Nat) (a : α) :
    ((limitSubspace head₀ L).blocks i).eval a =
      (a :: evalWord a (afterFirstParameter (L i).word)) ++
        (L (i + 1)).star := by
  change
    a :: evalWord a
      (afterFirstParameter (L i).word ++ constants (L (i + 1)).star) =
      (a :: evalWord a (afterFirstParameter (L i).word)) ++
        (L (i + 1)).star
  rw [Subspace.evalWord_append, evalWord_constants]
  rfl

/-- The star prefix at level `i`, followed by the remaining block evaluation,
is exactly the line-chain value starting at `i`. -/
theorem star_append_limit_evalFrom
    (head₀ : List α) (L : Nat → StarLine α)
    (i : Nat) (u : List α) :
    (L i).star ++ (limitSubspace head₀ L).evalFrom i u =
      lineChain L i u := by
  induction u generalizing i with
  | nil =>
      simp [Subspace.evalFrom, lineChain]
  | cons a u ih =>
      simp only [Subspace.evalFrom, lineChain]
      rw [limitSubspace_block_eval,
        StarLine.eval_eq_star_parameter_tail]
      rw [← ih (i + 1)]
      simp [List.append_assoc]

/-- Evaluation of the infinite limit has the explicit line-chain form. -/
theorem limitSubspace_eval
    (head₀ : List α) (L : Nat → StarLine α) (u : List α) :
    (limitSubspace head₀ L).eval u =
      head₀ ++ lineChain L 0 u := by
  unfold Subspace.eval
  change
    (head₀ ++ (L 0).star) ++
        (limitSubspace head₀ L).evalFrom 0 u =
      head₀ ++ lineChain L 0 u
  rw [List.append_assoc, star_append_limit_evalFrom]

/-- Successively extend a finite 0-variable word by the lines `L₀,L₁,...`. -/
def extendChain
    (U₀ : FiniteVariableWord α 0) (L : Nat → StarLine α) :
    (n : Nat) → FiniteVariableWord α n
  | 0 => U₀
  | n + 1 => (extendChain U₀ L n).extendByLine (L n)

@[simp] theorem extendChain_zero
    (U₀ : FiniteVariableWord α 0) (L : Nat → StarLine α) :
    extendChain U₀ L 0 = U₀ := rfl

@[simp] theorem extendChain_succ
    (U₀ : FiniteVariableWord α 0) (L : Nat → StarLine α) (n : Nat) :
    extendChain U₀ L (n + 1) =
      (extendChain U₀ L n).extendByLine (L n) := rfl

/-- Exact-length evaluation of the `n`th finite stage is the concatenation
of the first `n` line evaluations. -/
theorem extendChain_eval_exact
    (U₀ : FiniteVariableWord α 0) (L : Nat → StarLine α)
    (n : Nat) (u : List α) (hu : u.length = n) :
    (extendChain U₀ L n).eval u =
      U₀.eval [] ++ lineBodyChain L 0 u := by
  induction n generalizing u with
  | zero =>
      have hu0 : u = [] := List.length_eq_zero_iff.mp hu
      subst u
      simp [lineBodyChain]
  | succ n ih =>
      have hnlt : n < u.length := by omega
      let p := u.take n
      let a : α := u[n]
      have hp : p.length = n := by
        dsimp [p]
        simp [List.length_take, Nat.min_eq_left (by omega : n ≤ u.length)]
      have hsplit : p ++ [a] = u := by
        dsimp [p, a]
        calc
          u.take n ++ [u[n]] = u.take (n + 1) :=
            List.take_concat_get' u n hnlt
          _ = u := by simp [hu]
      rw [← hsplit]
      change
        ((extendChain U₀ L n).extendByLine (L n)).eval (p ++ [a]) =
          U₀.eval [] ++ lineBodyChain L 0 (p ++ [a])
      rw [FiniteVariableWord.extendByLine_eval_append_letter
          (extendChain U₀ L n) (L n) p a hp,
        ih p hp,
        lineBodyChain_append_last]
      simp [hp, List.append_assoc]

/-- The actual infinite subspace associated with the chain. -/
def greedyLimit
    (U₀ : FiniteVariableWord α 0) (L : Nat → StarLine α) :
    Subspace α :=
  limitSubspace (U₀.eval []) L

/-- Every finite evaluation of the infinite greedy limit agrees with the next
finite stage in the extension chain. -/
theorem greedyLimit_eval_eq_next_stage
    (U₀ : FiniteVariableWord α 0) (L : Nat → StarLine α)
    (u : List α) :
    (greedyLimit U₀ L).eval u =
      (extendChain U₀ L (u.length + 1)).eval u := by
  rw [greedyLimit, limitSubspace_eval,
    lineChain_eq_body_append_star]
  change
    U₀.eval [] ++
        (lineBodyChain L 0 u ++ (L (0 + u.length)).star) =
      ((extendChain U₀ L u.length).extendByLine (L u.length)).eval u
  rw [FiniteVariableWord.extendByLine_eval_of_length_eq
      (extendChain U₀ L u.length) (L u.length) u rfl,
    extendChain_eval_exact U₀ L u.length u rfl]
  simp [List.append_assoc]

end HalesJewett
end SuccessorTree
