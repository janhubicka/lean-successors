import SuccessorTree.Tree
import Mathlib.Tactic

/-!
# Original witnesses for nontrivial meets

These facts use the actual `LevelTree` interface of the successor library.
They have no H-construction hypotheses and make no choice of representatives.
They justify passing from nontrivial meets of prefixes to meets of originals.
The application must still show that its maintained original pool represents
all nodes introduced by parameter closure.
-/

namespace SuccessorTree.V10

universe u
variable {T : Type u} [PartialOrder T] [LevelTree T]

/-- Extending both operands cannot change a meet that was strictly below
both original operands. The common-component premise is essential in a forest. -/
theorem meet_eq_of_nontrivial_prefixes
    {s t a b : T}
    (hcommon : ∃ c : T, c ≤ s ∧ c ≤ t)
    (hsa : s ≤ a) (htb : t ≤ b)
    (hleft : LevelTree.meet s t ≠ s)
    (hright : LevelTree.meet s t ≠ t) :
    LevelTree.meet a b = LevelTree.meet s t := by
  have hxs := LevelTree.meet_le_left hcommon
  have hxt := LevelTree.meet_le_right hcommon
  obtain ⟨v, hxv, hvs⟩ :=
    LevelTree.exists_covBy_between (lt_of_le_of_ne hxs hleft)
  obtain ⟨w, hxw, hwt⟩ :=
    LevelTree.exists_covBy_between (lt_of_le_of_ne hxt hright)
  have hvw : v ≠ w := by
    intro h
    have hvt : v ≤ t := by simpa only [h] using hwt
    have hvx : v ≤ LevelTree.meet s t := LevelTree.le_meet hvs hvt
    exact (not_le_of_gt hxv.lt) hvx
  apply le_antisymm
  · exact LevelTree.meet_le_of_distinct_covBy hxv hxw hvw
      (hvs.trans hsa) (hwt.trans htb)
  · exact LevelTree.le_meet (hxs.trans hsa) (hxt.trans htb)

/-- Prefixes represented by a fixed pool of originals. -/
def prefixesOf (V : Set T) : Set T := {x | ∃ v ∈ V, x ≤ v}

/-- Taking a meet in one root component preserves its original pool. -/
theorem meet_mem_prefixesOf
    {V : Set T} {s t : T}
    (hs : s ∈ prefixesOf V) (ht : t ∈ prefixesOf V)
    (hcommon : ∃ c : T, c ≤ s ∧ c ≤ t) :
    LevelTree.meet s t ∈ prefixesOf V := by
  obtain ⟨a, ha, hsa⟩ := hs
  exact ⟨a, ha, (LevelTree.meet_le_left hcommon).trans hsa⟩

/-- Every nontrivial meet of represented prefixes is already the meet of
two members of the representing pool. This applies at every iteration. -/
theorem nontrivial_meet_has_originals
    {V : Set T} {s t : T}
    (hs : s ∈ prefixesOf V) (ht : t ∈ prefixesOf V)
    (hcommon : ∃ c : T, c ≤ s ∧ c ≤ t)
    (hleft : LevelTree.meet s t ≠ s)
    (hright : LevelTree.meet s t ≠ t) :
    ∃ a ∈ V, ∃ b ∈ V,
      (∃ c : T, c ≤ a ∧ c ≤ b) ∧
      LevelTree.meet s t = LevelTree.meet a b := by
  obtain ⟨a, ha, hsa⟩ := hs
  obtain ⟨b, hb, htb⟩ := ht
  refine ⟨a, ha, b, hb, ?_, ?_⟩
  · obtain ⟨c, hcs, hct⟩ := hcommon
    exact ⟨c, hcs.trans hsa, hct.trans htb⟩
  · exact (meet_eq_of_nontrivial_prefixes hcommon hsa htb hleft hright).symm

end SuccessorTree.V10
