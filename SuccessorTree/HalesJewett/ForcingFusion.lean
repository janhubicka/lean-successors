import SuccessorTree.HalesJewett.ForcingLemmaTwo
import Mathlib.Tactic

/-!
# Fusion schedule and recursive bad-line refinement

The forcing proof only needs a surjective enumeration of starred lines.  It is
not necessary to enumerate them by nondecreasing length.  Instead we attach to
stage i an increasing fusion level which dominates the length of every line
seen up to that stage.  Refinement is performed at this fusion level.

This removes the finite-by-length sorting bookkeeping from Lemma 2 while
retaining exactly the stabilization required by the fusion argument.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- A surjective enumeration of all starred lines. -/
structure LineSchedule (α : Type u) where
  line : Nat → StarLine α
  covers : ∀ L : StarLine α, ∃ i : Nat, line i = L

namespace LineSchedule

/-- Increasing shift level used at stage i.  It is positive, strictly
increasing, and dominates the raw length of the current line. -/
def fusionLevel (S : LineSchedule α) : Nat → Nat
  | 0 => max 1 (S.line 0).word.length
  | i + 1 => max (S.fusionLevel i + 1) (S.line (i + 1)).word.length

theorem line_length_le_level (S : LineSchedule α) (i : Nat) :
    (S.line i).word.length ≤ S.fusionLevel i := by
  cases i with
  | zero =>
      simp [fusionLevel]
  | succ i =>
      simp [fusionLevel]

theorem level_lt_succ (S : LineSchedule α) (i : Nat) :
    S.fusionLevel i < S.fusionLevel (i + 1) := by
  rw [fusionLevel]
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

theorem level_mono (S : LineSchedule α) :
    Monotone S.fusionLevel :=
  monotone_nat_of_le_succ fun i => Nat.le_of_lt (S.level_lt_succ i)

theorem index_lt_level (S : LineSchedule α) (i : Nat) :
    i < S.fusionLevel i := by
  induction i with
  | zero =>
      simp [fusionLevel]
  | succ i ih =>
      exact lt_of_le_of_lt (Nat.succ_le_iff.mpr ih) (S.level_lt_succ i)

theorem level_pos (S : LineSchedule α) (i : Nat) :
    0 < S.fusionLevel i :=
  lt_of_le_of_lt (Nat.zero_le i) (S.index_lt_level i)

theorem line_length_le_level_of_le
    (S : LineSchedule α) {j i : Nat} (h : j ≤ i) :
    (S.line j).word.length ≤ S.fusionLevel i :=
  le_trans (S.line_length_le_level j) (S.level_mono h)

theorem block_lt_level_of_lt
    (S : LineSchedule α) {k i : Nat} (h : k < i) :
    k + 1 < S.fusionLevel i := by
  have hk : k + 1 ≤ i := Nat.succ_le_iff.mpr h
  exact lt_of_le_of_lt hk (S.index_lt_level i)

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

/-- One non-large refinement step at a chosen shift level. -/
noncomputable def fusionStep
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) (n : Nat) : Subspace α :=
  W.compose ((chosenFusionRefiner A hNo W L).shift n)

/-- Recursive sequence of shifted refinements along a line schedule. -/
noncomputable def fusionSeq
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) : Nat → Subspace α
  | 0 => Subspace.identity
  | i + 1 =>
      fusionStep A hNo (fusionSeq A hNo S i) (S.line i) (S.fusionLevel i)

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
      fusionStep A hNo (fusionSeq A hNo S i) (S.line i)
        (S.fusionLevel i) := rfl

/-- A scheduled line is bad at every tail in a subspace. -/
def ScheduledBad
    (A : Set (List α)) (S : LineSchedule α)
    (W : Subspace α) (j : Nat) : Prop :=
  ∀ v : List α, ¬ lineTailGood W (S.line j) v A

/-- If a line is bad at every tail, shifting at any level at least its raw
length preserves this badness. -/
theorem fusionStep_preserves_line_bad
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) (n : Nat)
    (hL : L.word.length ≤ n)
    (hbad : ∀ t : List α, ¬ lineTailGood W L t A) :
    ∀ v : List α, ¬ lineTailGood (fusionStep A hNo W L n) L v A := by
  let U := chosenFusionRefiner A hNo W L
  exact compose_shift_preserves_line_bad A W U n L hL hbad

/-- The freshly scheduled line becomes bad after its own refinement step. -/
theorem fusionStep_current_bad
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (W : Subspace α) (L : StarLine α) (n : Nat)
    (hL : L.word.length ≤ n) :
    ∀ v : List α,
      ¬ lineTailGood (fusionStep A hNo W L n) L v A := by
  let U := chosenFusionRefiner A hNo W L
  have hU := chosenFusionRefiner_avoids A hNo W L
  exact compose_shift_preserves_line_bad A W U n L hL hU

/-- Earlier scheduled badness is preserved at a later fusion stage because
the fusion level dominates every line already seen. -/
theorem fusionStep_preserves_earlier_bad
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α)
    (W : Subspace α) {j i : Nat}
    (hji : j ≤ i)
    (hbad : ScheduledBad A S W j) :
    ScheduledBad A S
      (fusionStep A hNo W (S.line i) (S.fusionLevel i)) j := by
  let U := chosenFusionRefiner A hNo W (S.line i)
  exact compose_shift_preserves_line_bad
    A W U (S.fusionLevel i) (S.line j)
    (S.line_length_le_level_of_le hji) hbad

/-- Main recursive invariant: after stage i, every line scheduled strictly
before i is bad at every tail. -/
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
          A hNo (fusionSeq A hNo S i) (S.line i) (S.fusionLevel i)
          (S.line_length_le_level i)
      · have hjlt : j < i := by omega
        exact fusionStep_preserves_earlier_bad
          A hNo S (fusionSeq A hNo S i)
          (Nat.le_of_lt hjlt) (ih j hjlt)

end HalesJewett
end SuccessorTree
