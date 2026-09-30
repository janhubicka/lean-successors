import SuccessorTree.HalesJewett.ForcingFusion
import SuccessorTree.HalesJewett.ForcingMaximal
import Mathlib.Tactic

/-!
# Fusion limit for forcing Lemma 2

The fusion level at stage i is strictly above i. Therefore every fixed block k
is unchanged by all steps from stage k+1 onward. This gives a direct blockwise
fusion limit without sorting the line enumeration by length.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- Every fusion stage keeps the empty constant head. -/
theorem fusionSeq_head_eq_nil
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) :
    ∀ i : Nat, (fusionSeq A hNo S i).head = [] := by
  intro i
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      rw [fusionSeq_succ]
      unfold fusionStep
      rw [Subspace.compose_shift_head_eq]
      · exact ih
      · exact S.level_pos i

/-- One fusion step literally preserves every block strictly below its fusion
level. -/
theorem fusionSeq_block_succ_eq
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α)
    (i k : Nat)
    (h : k + 1 < S.fusionLevel i) :
    (fusionSeq A hNo S (i + 1)).blocks k =
      (fusionSeq A hNo S i).blocks k := by
  rw [fusionSeq_succ]
  unfold fusionStep
  exact Subspace.compose_shift_blocks_eq
    (fusionSeq A hNo S i)
    (chosenFusionRefiner A hNo (fusionSeq A hNo S i) (S.line i))
    (S.fusionLevel i) k h

/-- Block k is permanent from any stage p with k+1 <= p onward. -/
theorem fusionSeq_block_eq_of_le
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α)
    (k p q : Nat)
    (hstable : k + 1 ≤ p)
    (hpq : p ≤ q) :
    (fusionSeq A hNo S q).blocks k =
      (fusionSeq A hNo S p).blocks k := by
  induction q generalizing p with
  | zero =>
      have hp : p = 0 := by omega
      subst p
      rfl
  | succ q ih =>
      by_cases hp : p = q + 1
      · subst p
        rfl
      · have hpq' : p ≤ q := by omega
        have hkq : k + 1 ≤ q := le_trans hstable hpq'
        have hlevel : k + 1 < S.fusionLevel q :=
          lt_of_le_of_lt hkq (S.index_lt_level q)
        calc
          (fusionSeq A hNo S (q + 1)).blocks k =
              (fusionSeq A hNo S q).blocks k :=
            fusionSeq_block_succ_eq A hNo S q k hlevel
          _ = (fusionSeq A hNo S p).blocks k :=
            ih p hstable hpq'

/-- The direct blockwise fusion limit. -/
noncomputable def fusionLimit
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α) : Subspace α where
  head := []
  blocks := fun k =>
    (fusionSeq A hNo S (k + 1)).blocks k

theorem fusionLimit_block_eq_of_stage_ge
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α)
    (k n : Nat)
    (h : k + 1 ≤ n) :
    (fusionLimit A hNo S).blocks k =
      (fusionSeq A hNo S n).blocks k := by
  change
    (fusionSeq A hNo S (k + 1)).blocks k =
      (fusionSeq A hNo S n).blocks k
  exact (fusionSeq_block_eq_of_le
    A hNo S k (k + 1) n le_rfl h).symm

namespace Subspace

/-- Equality of the relevant block window implies equality of evalFrom. -/
theorem evalFrom_eq_of_blocks
    (W V : Subspace α) (base : Nat) (u : List α)
    (h : ∀ j : Nat, j < u.length →
      W.blocks (base + j) = V.blocks (base + j)) :
    W.evalFrom base u = V.evalFrom base u := by
  induction u generalizing base with
  | nil =>
      rfl
  | cons a u ih =>
      have h0 : W.blocks base = V.blocks base := by
        simpa using h 0 (by simp)
      have htail : ∀ j : Nat, j < u.length →
          W.blocks ((base + 1) + j) =
            V.blocks ((base + 1) + j) := by
        intro j hj
        have hjlen : j + 1 < (a :: u).length := by
          simpa using Nat.succ_lt_succ hj
        have hj' := h (j + 1) hjlen
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hj'
      change
        (W.blocks base).eval a ++ W.evalFrom (base + 1) u =
          (V.blocks base).eval a ++ V.evalFrom (base + 1) u
      rw [h0, ih (base + 1) htail]

/-- Equality of the head and all blocks used by a finite word implies equality
of its evaluation. -/
theorem eval_eq_of_head_blocks
    (W V : Subspace α) (u : List α)
    (hhead : W.head = V.head)
    (hblocks : ∀ k : Nat, k < u.length → W.blocks k = V.blocks k) :
    W.eval u = V.eval u := by
  change W.head ++ W.evalFrom 0 u = V.head ++ V.evalFrom 0 u
  rw [hhead]
  congr 1
  apply evalFrom_eq_of_blocks
  intro j hj
  simpa using hblocks j hj

end Subspace

/-- Every finite evaluation of the fusion limit agrees with every stage whose
index is at least the input length. -/
theorem fusionLimit_eval_eq_of_stage_ge
    (A : Set (List α))
    (hNo : ∀ W : Subspace α, ¬ HasLargePlus W A)
    (S : LineSchedule α)
    (u : List α) (n : Nat)
    (h : u.length ≤ n) :
    (fusionLimit A hNo S).eval u =
      (fusionSeq A hNo S n).eval u := by
  apply Subspace.eval_eq_of_head_blocks
  · rw [fusionSeq_head_eq_nil]
    rfl
  · intro k hk
    apply fusionLimit_block_eq_of_stage_ge
    exact le_trans (Nat.succ_le_of_lt hk) h

/-- The fusion contradiction closes Lemma 2 for any surjective line
enumeration. -/
theorem exists_hasLargePlus_of_schedule
    [Fintype α] [DecidableEq α]
    (A : Set (List α))
    (hlarge : WordLarge A)
    (hjProduct : ∀ n : Nat, StarHJ α (ExactWord α n → Bool))
    (S : LineSchedule α) :
    ∃ W : Subspace α, HasLargePlus W A := by
  classical
  by_contra hnone
  have hNo : ∀ W : Subspace α, ¬ HasLargePlus W A := by
    intro W hW
    exact hnone ⟨W, hW⟩

  let Wlim : Subspace α := fusionLimit A hNo S
  let B : Set (List α) := {v | Wlim.eval v ∈ A}

  have hB : WordLarge B := by
    have hpull :=
      (subspaceAction α).large_pullback
        (show (subspaceAction α).Large A from hlarge) Wlim
    change (subspaceAction α).Large B
    simpa [B, SubspaceAction.pullback, subspaceAction] using hpull

  obtain ⟨L, hLstar, hLeval⟩ :=
    large_set_contains_line B hB hjProduct
  obtain ⟨j, hj⟩ := S.covers L

  let N : Nat := max (j + 1) L.word.length
  have hjN : j < N := by
    dsimp [N]
    omega
  have hwordN : L.word.length ≤ N := by
    dsimp [N]
    exact le_max_right _ _

  have hbad :=
    fusionSeq_bad_before A hNo S N j hjN
  unfold ScheduledBad at hbad
  rw [hj] at hbad
  apply hbad []

  constructor
  · change Wlim.eval L.star ∈ A at hLstar
    have hsN : L.star.length ≤ N :=
      le_trans L.length_star_le_word_length hwordN
    have heq :=
      fusionLimit_eval_eq_of_stage_ge A hNo S L.star N hsN
    simpa [Wlim, heq] using hLstar
  · intro c
    have hc : Wlim.eval (L.eval c) ∈ A := hLeval c
    have hcN : (L.eval c).length ≤ N := by
      rw [L.length_eval]
      exact hwordN
    have heq :=
      fusionLimit_eval_eq_of_stage_ge A hNo S (L.eval c) N hcN
    simpa [Wlim, heq] using hc

end HalesJewett
end SuccessorTree
