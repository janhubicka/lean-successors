import SuccessorTree.HalesJewett.FiniteVariableWord
import SuccessorTree.Support
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# The maximal-avoider core of forcing Lemma 1

This file formalizes the central finite-colouring step in Lemma 1 of
Hubička--Smolík.  Starting from a finite variable word `U` which avoids a
large set and cannot be extended by one more variable while still avoiding
that set, the starred one-dimensional Hales--Jewett theorem produces a line
inside the set.

The existence of such a maximal avoider from largeness is deliberately kept
as the next, separate forcing lemma.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- A fixed-length word, represented in the finite function form used as the
colour coordinate in Lemma 1. -/
abbrev ExactWord (α : Type u) (n : Nat) := Fin n → α

/-- Convert a list whose length is exactly `n` into a fixed-length word. -/
def exactWordOfList (u : List α) {n : Nat} (h : u.length = n) :
    ExactWord α n :=
  fun i => u.get ⟨i.1, by simpa [h] using i.2⟩

@[simp] theorem ofFn_exactWordOfList
    (u : List α) {n : Nat} (h : u.length = n) :
    List.ofFn (exactWordOfList u h) = u := by
  subst n
  simpa [exactWordOfList] using (List.ofFn_get u)

/-- A finite `n`-variable word avoids `A` when none of its evaluations
using at most `n` supplied letters lies in `A`. -/
def FiniteVariableWord.Avoids
    (U : FiniteVariableWord α n) (A : Set (List α)) : Prop :=
  ∀ u : List α, u.length ≤ n → U.eval u ∉ A

/-- The product colouring from Lemma 1:
for a tail `v`, record for every exact `n`-word `u` whether
`U(u) ⌢ v` lies in `A`. -/
def productColour
    (U : FiniteVariableWord α n) (A : Set (List α))
    [DecidablePred (· ∈ A)]
    (v : List α) : ExactWord α n → Bool :=
  fun u => decide (U.eval (List.ofFn u) ++ v ∈ A)

/-- The key finite step of Lemma 1.

If `U` avoids `A` but every one-variable extension `U ⌢ L(λ_n)`
fails to avoid `A`, then starred Hales--Jewett produces a line all of whose
star/evaluation values lie in `A`.
-/
theorem line_mem_of_maximal_avoider
    [Fintype α]
    (A : Set (List α))
    (U : FiniteVariableWord α n)
    (havoid : U.Avoids A)
    (hmax : ∀ L : StarLine α, ¬ (U.extendByLine L).Avoids A)
    (hj : StarHJ α (ExactWord α n → Bool)) :
    ∃ K : StarLine α, K.star ∈ A ∧ ∀ a : α, K.eval a ∈ A := by
  classical
  let colour : List α → (ExactWord α n → Bool) :=
    productColour U A
  obtain ⟨L, hmono⟩ := hj colour

  have hex : ∃ q : ExactWord α n, colour L.star q = true := by
    by_contra hnone
    have hfalse : ∀ q : ExactWord α n, colour L.star q = false := by
      intro q
      cases hq : colour L.star q with
      | false => rfl
      | true =>
          exact False.elim (hnone ⟨q, hq⟩)

    have hext : (U.extendByLine L).Avoids A := by
      intro x hx
      by_cases hlt : x.length < n
      · rw [FiniteVariableWord.extendByLine_eval_of_length_lt U L x hlt]
        exact havoid x (Nat.le_of_lt hlt)
      · have hge : n ≤ x.length := Nat.le_of_not_gt hlt
        have hcases : x.length = n ∨ x.length = n + 1 := by
          omega
        rcases hcases with hn | hn1
        · rw [FiniteVariableWord.extendByLine_eval_of_length_eq U L x hn]
          let q : ExactWord α n := exactWordOfList x hn
          have hq := hfalse q
          change decide
              (U.eval (List.ofFn q) ++ L.star ∈ A) = false at hq
          rw [ofFn_exactWordOfList x hn] at hq
          exact of_decide_eq_false hq
        · have hnlt : n < x.length := by omega
          let p := x.take n
          let a : α := x[n]
          have hp : p.length = n := by
            dsimp [p]
            simp [List.length_take, Nat.min_eq_left hge]
          have hsplit : p ++ [a] = x := by
            dsimp [p, a]
            calc
              x.take n ++ [x[n]] = x.take (n + 1) :=
                List.take_concat_get' x n hnlt
              _ = x := by simp [hn1]
          rw [← hsplit,
            FiniteVariableWord.extendByLine_eval_append_letter U L p a hp]
          let q : ExactWord α n := exactWordOfList p hp
          have hcolour : colour (L.eval a) q = false := by
            calc
              colour (L.eval a) q = colour L.star q :=
                congrFun (hmono a) q
              _ = false := hfalse q
          change decide
              (U.eval (List.ofFn q) ++ L.eval a ∈ A) = false at hcolour
          rw [ofFn_exactWordOfList p hp] at hcolour
          exact of_decide_eq_false hcolour

    exact False.elim ((hmax L) hext)

  obtain ⟨q, hq⟩ := hex
  let prefix := U.eval (List.ofFn q)
  refine ⟨L.prepend prefix, ?_, ?_⟩
  · have hmem : prefix ++ L.star ∈ A := by
      change decide (prefix ++ L.star ∈ A) = true at hq
      exact of_decide_eq_true hq
    simpa [prefix] using hmem
  · intro a
    have hqa : colour (L.eval a) q = true := by
      calc
        colour (L.eval a) q = colour L.star q := congrFun (hmono a) q
        _ = true := hq
    have hmem : prefix ++ L.eval a ∈ A := by
      change decide (prefix ++ L.eval a ∈ A) = true at hqa
      exact of_decide_eq_true hqa
    simpa [prefix] using hmem

end HalesJewett
end SuccessorTree
