import SuccessorTree.V10.FiniteKptLevels
import SuccessorTree.V10.RawPrefixOrder
import Mathlib.Tactic

/-!
# The genuine greatest common predecessor on raw finite L+ types

Raw complete partial types have a proved prefix partial order,
comparable predecessors, a unique ancestor on each lower level,
and finite levels. Here we construct the actual meet operation.

For nodes having a common predecessor, the maximal common level
is found using Nat.findGreatest, and the chosen node at that level
is proved to be below BOTH operands and above EVERY other common
predecessor. If no common predecessor exists, the total operation
uses a fixed empty raw root; the laws needed by LevelTree are only
claimed when a common predecessor exists.

No new meet or forest axiom is introduced, and no assertion that
an arbitrary raw L+ record is an admissible Kpt node is made.
-/

namespace SuccessorTree.V10

/-- An arbitrary canonical raw root, needed only to totalize the
meet of two nodes in different root components. -/
def rawEmptyTypeNode (db du dd : Nat) :
    RawPartialTypeNode db du dd :=
  ⟨0,
    { lReduct :=
        { binary := fun _ _ _ => false
          unary := fun _ _ => false
          diagonal := fun _ _ => false }
      eRelation := fun _ _ => false }⟩

/-- There is a common raw prefix at exactly the indicated level. -/
def RawCommonLevel
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd)
    (n : Nat) : Prop :=
  ∃ c : RawPartialTypeNode db du dd,
    c ≤ a ∧ c ≤ b ∧ c.1 = n

/-- Any two nodes with a common predecessor also have a common
predecessor on level zero. -/
theorem rawCommonLevel_zero_of_common
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd)
    (hCommon : ∃ c, c ≤ a ∧ c ≤ b) :
    RawCommonLevel a b 0 := by
  obtain ⟨c, hca, hcb⟩ := hCommon
  let root := rawPartialTypeAncestor c 0 (Nat.zero_le c.1)
  refine ⟨root, ?_, ?_, rfl⟩
  · exact (rawPartialTypeAncestor_le c 0 (Nat.zero_le c.1)).trans hca
  · exact (rawPartialTypeAncestor_le c 0 (Nat.zero_le c.1)).trans hcb

/-- The greatest common prefix level when a common prefix exists.
For disjoint root components the numerical value is irrelevant. -/
noncomputable def rawMeetLevel
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd) : Nat :=
  by
    classical
    exact if h : ∃ c, c ≤ a ∧ c ≤ b then
      Nat.findGreatest (RawCommonLevel a b) (min a.1 b.1)
    else 0

theorem rawMeetLevel_common
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd)
    (hCommon : ∃ c, c ≤ a ∧ c ≤ b) :
    RawCommonLevel a b (rawMeetLevel a b) := by
  classical
  unfold rawMeetLevel
  rw [dif_pos hCommon]
  apply Nat.findGreatest_spec (m := 0)
  · exact Nat.zero_le _
  · exact rawCommonLevel_zero_of_common a b hCommon

/-- The chosen greatest common raw prefix; the fallback in a
disjoint root component never occurs in meet-law hypotheses. -/
noncomputable def rawMeet
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd) :
    RawPartialTypeNode db du dd :=
  by
    classical
    exact if h : ∃ c, c ≤ a ∧ c ≤ b then
      Classical.choose (rawMeetLevel_common a b h)
    else rawEmptyTypeNode db du dd

theorem rawMeet_spec
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd)
    (hCommon : ∃ c, c ≤ a ∧ c ≤ b) :
    rawMeet a b ≤ a ∧ rawMeet a b ≤ b ∧
      (rawMeet a b).1 = rawMeetLevel a b := by
  classical
  unfold rawMeet
  rw [dif_pos hCommon]
  exact Classical.choose_spec (rawMeetLevel_common a b hCommon)

theorem rawMeet_le_left
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd)
    (hCommon : ∃ c, c ≤ a ∧ c ≤ b) :
    rawMeet a b ≤ a :=
  (rawMeet_spec a b hCommon).1

theorem rawMeet_le_right
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd)
    (hCommon : ∃ c, c ≤ a ∧ c ≤ b) :
    rawMeet a b ≤ b :=
  (rawMeet_spec a b hCommon).2.1

/-- Every other common prefix is below the chosen maximal raw
prefix; this is the universal property of a genuine meet. -/
theorem raw_le_meet
    {db du dd : Nat}
    {a b c : RawPartialTypeNode db du dd}
    (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ rawMeet a b := by
  classical
  have hCommon : ∃ x, x ≤ a ∧ x ≤ b := ⟨c, hca, hcb⟩
  obtain ⟨hma, _, hlev⟩ := rawMeet_spec a b hCommon
  have hbound : c.1 ≤ min a.1 b.1 :=
    Nat.le_min.mpr
      ⟨rawPartialTypePrefix_level_le hca,
        rawPartialTypePrefix_level_le hcb⟩
  have hmax : c.1 ≤ rawMeetLevel a b := by
    unfold rawMeetLevel
    rw [dif_pos hCommon]
    exact Nat.le_findGreatest hbound ⟨c, hca, hcb, rfl⟩
  have hcle : c.1 ≤ (rawMeet a b).1 := by
    rw [hlev]
    exact hmax
  rcases rawPartialType_lower_linear hca hma with hcm | hmc
  · exact hcm
  · have hmcLev := rawPartialTypePrefix_level_le hmc
    have heqLevel : (rawMeet a b).1 = c.1 := by omega
    have heq := rawPartialTypePrefix_eq_of_same_level hmc heqLevel
    exact le_of_eq heq.symm

end SuccessorTree.V10
