import SuccessorTree.HalesJewett.GreedyLimit
import SuccessorTree.HalesJewett.ForcingLemmaOne
import SuccessorTree.HalesJewett.ForcingReduction
import Mathlib.Tactic

/-!
# Maximal avoiders and forcing Lemma 1

This file formalizes the greedy compactness argument at the start of
Hubička--Smolík Lemma 1.  If every finite avoiding variable word had an
avoiding one-variable extension, classical choice would build an infinite
subspace all of whose finite evaluations avoid the large set.  The
`GreedyLimit` identity makes that contradiction explicit.

Combining the resulting maximal avoider with the product-colouring theorem
from `ForcingLemmaOne.lean` yields the complete large-set line lemma.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- A finite variable word bundled with the fact that it avoids `A`. -/
structure AvoidingStage (A : Set (List α)) (n : Nat) where
  word : FiniteVariableWord α n
  avoids : word.Avoids A

/-- A chosen avoiding extension line, assuming every avoiding stage can be
extended. -/
noncomputable def chosenExtensionLine
    {A : Set (List α)}
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A)
    {n : Nat} (X : AvoidingStage A n) : StarLine α :=
  Classical.choose (extendable X)

theorem chosenExtensionLine_spec
    {A : Set (List α)}
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A)
    {n : Nat} (X : AvoidingStage A n) :
    (X.word.extendByLine (chosenExtensionLine extendable X)).Avoids A :=
  Classical.choose_spec (extendable X)

/-- Advance one step in the greedy avoiding chain. -/
noncomputable def nextAvoidingStage
    {A : Set (List α)}
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A)
    {n : Nat} (X : AvoidingStage A n) :
    AvoidingStage A (n + 1) where
  word := X.word.extendByLine (chosenExtensionLine extendable X)
  avoids := chosenExtensionLine_spec extendable X

/-- Recursively chosen avoiding stages. -/
noncomputable def greedyStages
    {A : Set (List α)}
    (X₀ : AvoidingStage A 0)
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A) :
    (n : Nat) → AvoidingStage A n
  | 0 => X₀
  | n + 1 => nextAvoidingStage extendable (greedyStages X₀ extendable n)

/-- The line chosen at stage `n`. -/
noncomputable def greedyLines
    {A : Set (List α)}
    (X₀ : AvoidingStage A 0)
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A)
    (n : Nat) : StarLine α :=
  chosenExtensionLine extendable (greedyStages X₀ extendable n)

/-- The recursively chosen stage is exactly the finite extension chain of the
chosen lines. -/
theorem greedyStages_word_eq_extendChain
    {A : Set (List α)}
    (X₀ : AvoidingStage A 0)
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A)
    (n : Nat) :
    (greedyStages X₀ extendable n).word =
      extendChain X₀.word (greedyLines X₀ extendable) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (greedyStages X₀ extendable n).word.extendByLine
            (greedyLines X₀ extendable n) =
          (extendChain X₀.word (greedyLines X₀ extendable) n).extendByLine
            (greedyLines X₀ extendable n)
      rw [ih]

/-- If every avoiding finite stage can be extended to another avoiding stage,
then `A` is not large. -/
theorem not_wordLarge_of_all_avoiders_extend
    {A : Set (List α)}
    (X₀ : AvoidingStage A 0)
    (extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A) :
    ¬ WordLarge A := by
  intro hlarge
  let L : Nat → StarLine α := greedyLines X₀ extendable
  let W : Subspace α := greedyLimit X₀.word L
  obtain ⟨u, hu⟩ := hlarge W
  change W.eval u ∈ A at hu
  have hstage :=
    (greedyStages X₀ extendable (u.length + 1)).avoids
      u (Nat.le_succ u.length)
  have hword :=
    greedyStages_word_eq_extendChain X₀ extendable (u.length + 1)
  have hnot :
      (extendChain X₀.word L (u.length + 1)).eval u ∉ A := by
    change
      (greedyStages X₀ extendable (u.length + 1)).word.eval u ∉ A at hstage
    rw [hword] at hstage
    exact hstage
  have hlim :
      W.eval u =
        (extendChain X₀.word L (u.length + 1)).eval u := by
    exact greedyLimit_eval_eq_next_stage X₀.word L u
  exact hnot (hlim ▸ hu)

/-- Largeness forces the greedy construction to stop at a maximal finite
avoider. -/
theorem exists_maximal_avoider_of_large
    {A : Set (List α)}
    (hlarge : WordLarge A)
    (X₀ : AvoidingStage A 0) :
    ∃ n : Nat, ∃ U : FiniteVariableWord α n,
      U.Avoids A ∧
        ∀ L : StarLine α, ¬ (U.extendByLine L).Avoids A := by
  classical
  by_contra hmax
  have extendable :
      ∀ {n : Nat} (X : AvoidingStage A n),
        ∃ L : StarLine α, (X.word.extendByLine L).Avoids A := by
    intro n X
    by_contra hL
    have hnone :
        ∀ L : StarLine α, ¬ (X.word.extendByLine L).Avoids A := by
      intro L hAvoid
      exact hL ⟨L, hAvoid⟩
    exact hmax ⟨n, X.word, X.avoids, hnone⟩
  exact (not_wordLarge_of_all_avoiders_extend X₀ extendable) hlarge

/-- A word outside `A` gives a 0-variable avoiding stage. -/
def zeroAvoidingStage
    {A : Set (List α)} (u : List α) (hu : u ∉ A) :
    AvoidingStage A 0 where
  word := FiniteVariableWord.zeroWord u
  avoids := by
    intro v hv
    simpa using hu

/-- If `A` is not the whole word space, it has a word outside it. -/
theorem exists_not_mem_of_ne_univ
    {A : Set (List α)} (hA : A ≠ Set.univ) :
    ∃ u : List α, u ∉ A := by
  classical
  by_contra h
  apply hA
  ext u
  constructor
  · intro _
    trivial
  · intro _
    by_contra hu
    exact h ⟨u, hu⟩

/-- Full forcing Lemma 1: assuming the one-dimensional starred theorem for
the finite product colour types used in its proof, every large set contains a
starred line. -/
theorem large_set_contains_line
    [Fintype α]
    (A : Set (List α))
    (hlarge : WordLarge A)
    (hjProduct :
      ∀ n : Nat, StarHJ α (ExactWord α n → Bool)) :
    ∃ K : StarLine α, K.star ∈ A ∧ ∀ a : α, K.eval a ∈ A := by
  classical
  by_cases hA : A = Set.univ
  · subst A
    let K : StarLine α :=
      ⟨[LineSymbol.parameter], by simp⟩
    refine ⟨K, ?_, ?_⟩
    · simp
    · intro a
      simp
  · obtain ⟨u₀, hu₀⟩ := exists_not_mem_of_ne_univ hA
    let X₀ : AvoidingStage A 0 := zeroAvoidingStage u₀ hu₀
    obtain ⟨n, U, hAvoid, hMax⟩ :=
      exists_maximal_avoider_of_large hlarge X₀
    exact line_mem_of_maximal_avoider
      A U hAvoid hMax (hjProduct n)

end HalesJewett
end SuccessorTree
