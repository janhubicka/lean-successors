import SuccessorTree.HalesJewett.Composition
import SuccessorTree.HalesJewett.ForcingReduction
import Mathlib.Tactic

/-!
# One-step refinement for forcing Lemma 2

This file formalizes the local induction step in Hubička--Smolík Lemma 2.

For a subspace `W`, a starred line `L`, and a set `A`, define
`lineTailGood W L v A` to mean that the star value and every one-letter
value of the line `L ⌢ v`, after substitution through `W`, lie in `A`.

There are two cases.

* If the set of good tails is large, composing `W` with the subspace whose
  first line is `L` already gives the desired conclusion of Lemma 2.
* If it is not large, choose a subspace `U` avoiding the good tails and
  refine by `W(Shift(U,|L|))`.  The new subspace is unchanged on every
  evaluation of length strictly below `|L|`, fails the current line
  condition, and preserves failure of all earlier lines of length at most
  `|L|`.

The strict inequality in the stabilization statement is the correction found
during Lean verification.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- The subspace whose first coordinate is the starred line `L`, followed by
identity coordinates. -/
def linePrefixSubspace (L : StarLine α) : Subspace α where
  head := L.star
  blocks := fun
    | 0 => ⟨afterFirstParameter L.word⟩
    | _ + 1 => ⟨[]⟩

@[simp] theorem linePrefixSubspace_evalFrom_succ
    (L : StarLine α) (i : Nat) (u : List α) :
    (linePrefixSubspace L).evalFrom (i + 1) u = u := by
  induction u generalizing i with
  | nil => rfl
  | cons a u ih =>
      change
        a :: (linePrefixSubspace L).evalFrom ((i + 1) + 1) u =
          a :: u
      exact congrArg (List.cons a) (ih (i + 1))

@[simp] theorem linePrefixSubspace_eval_nil
    (L : StarLine α) :
    (linePrefixSubspace L).eval [] = L.star := by
  simp [Subspace.eval, Subspace.evalFrom, linePrefixSubspace]

@[simp] theorem linePrefixSubspace_eval_cons
    (L : StarLine α) (a : α) (u : List α) :
    (linePrefixSubspace L).eval (a :: u) =
      L.eval a ++ u := by
  change
    L.star ++
        ((a :: evalWord a (afterFirstParameter L.word)) ++
          (linePrefixSubspace L).evalFrom 1 u) =
      L.eval a ++ u
  rw [linePrefixSubspace_evalFrom_succ,
    StarLine.eval_eq_star_parameter_tail]
  simp [List.append_assoc]

/-- The line `L ⌢ v` is good for `W,A` when its star value and every
letter evaluation land in `A`. -/
def lineTailGood
    (W : Subspace α) (L : StarLine α)
    (v : List α) (A : Set (List α)) : Prop :=
  W.eval L.star ∈ A ∧
    ∀ c : α, W.eval (L.eval c ++ v) ∈ A

/-- Set of tails on which a fixed line is good. -/
def lineGoodTails
    (W : Subspace α) (L : StarLine α)
    (A : Set (List α)) : Set (List α) :=
  {v | lineTailGood W L v A}

/-- The large tail set required in conclusion (II) of forcing Lemma 2. -/
def plusSet
    (W : Subspace α) (A : Set (List α)) : Set (List α) :=
  {v | ∀ c : α, W.eval (c :: v) ∈ A}

/-- Desired conclusion of forcing Lemma 2. -/
def HasLargePlus
    (W : Subspace α) (A : Set (List α)) : Prop :=
  W.eval [] ∈ A ∧ WordLarge (plusSet W A)

/-- If the current good-tail set is large, the proof stops successfully. -/
theorem hasLargePlus_of_lineGoodTails_large
    (A : Set (List α)) (W : Subspace α) (L : StarLine α)
    (hlarge : WordLarge (lineGoodTails W L A)) :
    ∃ W' : Subspace α, HasLargePlus W' A := by
  let V : Subspace α := linePrefixSubspace L
  let W' : Subspace α := W.compose V

  obtain ⟨v₀, hv₀⟩ := hlarge Subspace.identity
  have hvGood : lineTailGood W L v₀ A := by
    change lineTailGood W L ((Subspace.identity : Subspace α).eval v₀) A at hv₀
    simpa using hv₀

  refine ⟨W', ?_, ?_⟩
  · change (W.compose V).eval [] ∈ A
    rw [Subspace.compose_eval]
    change W.eval ((linePrefixSubspace L).eval []) ∈ A
    rw [linePrefixSubspace_eval_nil]
    exact hvGood.1
  · intro U
    obtain ⟨v, hv⟩ := hlarge U
    have hvGood' : lineTailGood W L (U.eval v) A := by
      exact hv
    refine ⟨v, ?_⟩
    change U.eval v ∈ plusSet W' A
    intro c
    change W'.eval (c :: U.eval v) ∈ A
    change (W.compose V).eval (c :: U.eval v) ∈ A
    rw [Subspace.compose_eval, linePrefixSubspace_eval_cons]
    exact hvGood'.2 c

/-- Non-largeness is witnessed by a concrete avoiding subspace. -/
theorem exists_subspace_avoiding_of_not_wordLarge
    (B : Set (List α)) (h : ¬ WordLarge B) :
    ∃ U : Subspace α, ∀ v : List α, U.eval v ∉ B := by
  change ¬ (subspaceAction α).Large B at h
  obtain ⟨U, hU⟩ :=
    ((subspaceAction α).not_large_iff_exists_avoids B).mp h
  refine ⟨U, ?_⟩
  intro v
  exact hU v

/-- Non-large current good-tail set gives a shifted refinement which is
strictly stable below `|L|` and makes the current line bad at every tail. -/
theorem refine_of_lineGoodTails_not_large
    (A : Set (List α)) (W : Subspace α) (L : StarLine α)
    (hnot : ¬ WordLarge (lineGoodTails W L A)) :
    ∃ U : Subspace α,
      let n := L.word.length
      let W' := W.compose (U.shift n)
      (∀ u : List α, u.length < n → W'.eval u = W.eval u) ∧
      (∀ v : List α, ¬ lineTailGood W' L v A) := by
  obtain ⟨U, hU⟩ :=
    exists_subspace_avoiding_of_not_wordLarge
      (lineGoodTails W L A) hnot
  refine ⟨U, ?_⟩
  dsimp
  constructor
  · intro u hu
    exact Subspace.compose_shift_eval_of_length_lt W U L.word.length u hu
  · intro v hnew
    have hAvoid := hU v
    apply hAvoid
    constructor
    · have hstar :=
        Subspace.compose_shift_eval_of_length_lt
          W U L.word.length L.star L.length_star_lt_word_length
      exact hstar ▸ hnew.1
    · intro c
      have hletter :=
        Subspace.compose_shift_eval_append
          W U L.word.length (L.eval c) v (L.length_eval c)
      exact hletter ▸ hnew.2 c

/-- A shifted refinement also preserves badness of any earlier line whose raw
length is at most the current shift level. -/
theorem compose_shift_preserves_line_bad
    (A : Set (List α))
    (W U : Subspace α) (n : Nat)
    (J : StarLine α)
    (hJlen : J.word.length ≤ n)
    (hbad : ∀ t : List α, ¬ lineTailGood W J t A) :
    ∀ v : List α,
      ¬ lineTailGood (W.compose (U.shift n)) J v A := by
  intro v hnew
  let t : List α :=
    (U.shift (n - J.word.length)).eval v
  apply hbad t
  constructor
  · have hstarLen : J.star.length < n := by
      exact lt_of_lt_of_le J.length_star_lt_word_length hJlen
    have hstar :=
      Subspace.compose_shift_eval_of_length_lt
        W U n J.star hstarLen
    exact hstar ▸ hnew.1
  · intro c
    have hp : (J.eval c).length ≤ n := by
      rw [J.length_eval]
      exact hJlen
    have heq :=
      Subspace.compose_shift_eval_append_of_length_le
        W U n (J.eval c) v hp
    have heq' :
        (W.compose (U.shift n)).eval (J.eval c ++ v) =
          W.eval (J.eval c ++ t) := by
      simpa [t, J.length_eval] using heq
    exact heq' ▸ hnew.2 c

end HalesJewett
end SuccessorTree
