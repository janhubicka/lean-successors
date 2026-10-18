import Mathlib.Tactic

/-!
# Independent visible levels and cutting marks

A mark at coordinate c denotes the gap immediately before level c.
A visible level l_i lies inside its marked block iff
c_i ≤ l_i < c_(i+1). The source-level and mark-index maps of a
reduction may differ. This file proves only index bookkeeping; legal
successor-block realization and Ramsey A4 are separate questions.
-/

namespace SuccessorTree.Block

structure MarkedLevelSchedule where
  level : Nat → Nat
  cut : Nat → Nat
  level_strict : StrictMono level
  cut_strict : StrictMono cut
  cut_zero : cut 0 = 0
  inside : ∀ i, cut i ≤ level i ∧ level i < cut (i + 1)

namespace MarkedLevelSchedule

theorem between_next (U : MarkedLevelSchedule) (i : Nat) :
    U.level i < U.cut (i + 1) ∧
    U.cut (i + 1) ≤ U.level (i + 1) :=
  ⟨(U.inside i).2, (U.inside (i+1)).1⟩

end MarkedLevelSchedule

/-! An index witness is necessary but not sufficient for a geometric
reduction: the full cone/label trace still has to be realized. -/
structure MarkedIndexReduction (V U : MarkedLevelSchedule) where
  treeIndex : Nat → Nat
  cutIndex : Nat → Nat
  tree_strict : StrictMono treeIndex
  cut_strict : StrictMono cutIndex
  cut_zero : cutIndex 0 = 0
  level_match : ∀ i, V.level i = U.level (treeIndex i)
  cut_match : ∀ i, V.cut i = U.cut (cutIndex i)
  interlace : ∀ i, cutIndex i ≤ treeIndex i ∧ treeIndex i < cutIndex (i+1)

namespace MarkedIndexReduction

def refl (U : MarkedLevelSchedule) : MarkedIndexReduction U U where
  treeIndex := id
  cutIndex := id
  tree_strict := strictMono_id
  cut_strict := strictMono_id
  cut_zero := rfl
  level_match := fun _ => rfl
  cut_match := fun _ => rfl
  interlace := by intro i; exact ⟨le_refl _, Nat.lt_succ_self _⟩

def comp {W V U : MarkedLevelSchedule}
    (WV : MarkedIndexReduction W V)
    (VU : MarkedIndexReduction V U) :
    MarkedIndexReduction W U where
  treeIndex := VU.treeIndex ∘ WV.treeIndex
  cutIndex := VU.cutIndex ∘ WV.cutIndex
  tree_strict := VU.tree_strict.comp WV.tree_strict
  cut_strict := VU.cut_strict.comp WV.cut_strict
  cut_zero := by simp [Function.comp_def, WV.cut_zero, VU.cut_zero]
  level_match := by intro i; exact (WV.level_match i).trans (VU.level_match _)
  cut_match := by intro i; exact (WV.cut_match i).trans (VU.cut_match _)
  interlace := by
    intro i
    obtain ⟨hleft, hright⟩ := WV.interlace i
    constructor
    · calc
        VU.cutIndex (WV.cutIndex i) ≤ VU.cutIndex (WV.treeIndex i) :=
          VU.cut_strict.monotone hleft
        _ ≤ VU.treeIndex (WV.treeIndex i) := (VU.interlace _).1
    · calc
        VU.treeIndex (WV.treeIndex i) < VU.cutIndex (WV.treeIndex i + 1) :=
          (VU.interlace _).2
        _ ≤ VU.cutIndex (WV.cutIndex (i+1)) :=
          VU.cut_strict.monotone (Nat.succ_le_iff.mpr hright)

end MarkedIndexReduction

/-! For separated variable supports there are genuinely many legal
numerical marks: after the last use of x_i and no later than the
first use of x_(i+1). This checks the interleaving, not the abstract
successor-map realization of each row. -/
structure SeparatedOccurrenceSchedule where
  first : Nat → Nat
  last : Nat → Nat
  first_le_last : ∀ i, first i ≤ last i
  last_before_next : ∀ i, last i < first (i+1)

namespace SeparatedOccurrenceSchedule

def AdmissibleCuts (W : SeparatedOccurrenceSchedule) (cut : Nat → Nat) : Prop :=
  cut 0 = 0 ∧ ∀ i, W.last i < cut (i+1) ∧ cut (i+1) ≤ W.first (i+1)

noncomputable def toMarked (W : SeparatedOccurrenceSchedule)
    (cut : Nat → Nat) (h : W.AdmissibleCuts cut) : MarkedLevelSchedule where
  level := W.first
  cut := cut
  level_strict := strictMono_nat_of_lt_succ (fun i =>
    lt_of_le_of_lt (W.first_le_last i) (W.last_before_next i))
  cut_strict := strictMono_nat_of_lt_succ (by
    intro i
    have hcut : cut i ≤ W.first i := by
      cases i with
      | zero => simp [h.1]
      | succ j => exact (h.2 j).2
    exact lt_of_le_of_lt (hcut.trans (W.first_le_last i)) (h.2 i).1)
  cut_zero := h.1
  inside := by
    intro i
    constructor
    · cases i with
      | zero => simp [h.1]
      | succ j => exact (h.2 j).2
    · exact lt_of_le_of_lt (W.first_le_last i) (h.2 i).1

end SeparatedOccurrenceSchedule

end SuccessorTree.Block
