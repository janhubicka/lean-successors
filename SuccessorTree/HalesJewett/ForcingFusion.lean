import SuccessorTree.HalesJewett.ForcingLemmaTwo
import Mathlib.Tactic

/-!
# Fusion schedule and recursive bad-line refinement

This file formalizes the recursive part of the fusion argument in
Hubička--Smolík Lemma 2.  The concrete enumeration of all starred lines is
kept separate; here we assume a schedule with exactly the three properties
used by the proof:

* every starred line occurs;
* raw line lengths are nondecreasing;
* raw line lengths eventually exceed every fixed bound.

Under the contradiction hypothesis that no subspace satisfies
`HasLargePlus`, every scheduled good-tail set is non-large.  We therefore
choose an avoiding refinement at every stage.  The main theorem in this file
says that after stage `i`, every scheduled line with index below `i` is bad
at every tail.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- Abstract line enumeration with the exact properties needed for fusion. -/
structure LineSchedule (α : Type u) where
  line : Nat → StarLine α
  covers : ∀ L : StarLine α, ∃ i : Nat, line i = L
  length_mono : Monotone (fun i => (line i).word.length)
  length_unbounded :
    ∀ r : Nat, ∃ N : Nat, ∀ i : Nat, N ≤ i → r < (line i).word.length

namespace LineSchedule

theorem length_le_of_le
    (S : LineSchedule α) {i j : Nat} (h : i ≤ j) :
    (S.line i).word.length ≤ (S.line j).word.length :=
  S.length_mono h

theorem length_pos (S : LineSchedule α) (i : Nat) :
    0 < (S.line i).word.length := by
  exact lt_of_le_of_lt (Nat.zero_le _) (S.line i).length_star_lt_word_length

end LineSchedule

/-- If no successful Lemma-2 subspace exists, no current good-tail set can be
large. -/
theorem lineGoodTails_not_large_of_no_solution
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) :
    ¬ WordLarge (lineGoodTails W L A) := by
  intro hlarge
  obtain ⟨W', hW'⟩ :=
    hasLargePlus_of_lineGoodTails_large A W L hlarge
  exact hNo W' hW'

/-- A chosen subspace avoiding the current scheduled good-tail set. -/
noncomputable def chosenFusionRefiner
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) : Subspace α :=
  Classical.choose <|
    exists_subspace_avoiding_of_not_wordLarge
      (lineGoodTails W L A)
      (lineGoodTails_not_large_of_no_solution A hNo W L)

theorem chosenFusionRefiner_avoids
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) :
    ∀ v : List α,
      (chosenFusionRefiner A hNo W L).eval v ∉ lineGoodTails W L A :=
  Classical.choose_spec <|
    exists_subspace_avoiding_of_not_wordLarge
      (lineGoodTails W L A)
      (lineGoodTails_not_large_of_no_solution A hNo W L)

/-- One non-large refinement step from the forcing proof. -/
noncomputable def fusionStep
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) : Subspace α :=
  W.compose ((chosenFusionRefiner A hNo W L).shift L.word.length)

/-- Recursive sequence of shifted refinements along a line schedule. -/
noncomputable def fusionSeq
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) : Nat → Subspace α
  | 0 => Subspace.identity
  | i + 1 => fusionStep A hNo (fusionSeq A hNo S i) (S.line i)

@[simp] theorem fusionSeq_zero
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) :
    fusionSeq A hNo S 0 = Subspace.identity := rfl

@[simp] theorem fusionSeq_succ
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) (i : Nat) :
    fusionSeq A hNo S (i + 1) =
      fusionStep A hNo (fusionSeq A hNo S i) (S.line i) := rfl

/-- A scheduled line is bad at every tail in a subspace. -/
def ScheduledBad
    (A : Set (List α)) (S : LineSchedule α)
    (W : Subspace α) (j : Nat) : Prop :=
  ∀ v : List α, ¬ lineTailGood W (S.line j) v A

/-- The freshly scheduled line becomes bad after its own refinement step. -/
theorem fusionStep_current_bad
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) :
    ∀ v : List α,
      ¬ lineTailGood (fusionStep A hNo W L) L v A := by
  let U := chosenFusionRefiner A hNo W L
  have hU := chosenFusionRefiner_avoids A hNo W L
  intro v hnew
  apply hU v
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

/-- Earlier scheduled badness is preserved at a later nondecreasing-length
refinement stage. -/
theorem fusionStep_preserves_earlier_bad
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α)
    (W : Subspace α) {j i : Nat}
    (hji : j ≤ i)
    (hbad : ScheduledBad A S W j) :
    ScheduledBad A S
      (fusionStep A hNo W (S.line i)) j := by
  let U := chosenFusionRefiner A hNo W (S.line i)
  exact compose_shift_preserves_line_bad
    A W U (S.line i).word.length (S.line j)
    (S.length_le_of_le hji) hbad

/-- Main recursive invariant: after stage `i`, every line scheduled strictly
before `i` is bad at every tail. -/
theorem fusionSeq_bad_before
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) :
    ∀ i j : Nat, j < i →
      ScheduledBad A S (fusionSeq A hNo S i) j := by
  intro i
  induction i with
  | zero =>
      intro j hj
      omega
  | succ i ih =>
      intro j hj
      by_cases hji : j = i
      · subst j
        exact fusionStep_current_bad
          A hNo (fusionSeq A hNo S i) (S.line i)
      · have hjlt : j < i := by omega
        exact fusionStep_preserves_earlier_bad
          A hNo S (fusionSeq A hNo S i)
          (Nat.le_of_lt hjlt) (ih j hjlt)

end HalesJewett
end SuccessorTree
