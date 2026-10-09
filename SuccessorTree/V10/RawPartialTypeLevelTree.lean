import SuccessorTree.V10.RawPrefixMeet
import SuccessorTree.Tree
import Mathlib.Tactic

/-!
# The first complete LevelTree representation of raw L+ partial types

The raw finite L+ types are dependent pairs (socle length,
complete structure over that socle and the type vertex).
The initial-socle prefix order is already proved to be
a partial order, and its meets were constructed separately.

Here we instantiate the manuscript's abstract LevelTree interface
by deriving each required property from the raw representation:
strict level growth, covers on consecutive levels,
comparability of predecessors, existence of every ancestor,
finiteness of each level, and greatest common predecessors.

In particular this is a complete literal finite-branching forest
representation, but it contains *all* raw L+ records and not just
the admissible forbidden-free Kpt family. That subforest will be
checked separately using the prefix-closure theorem.
-/

namespace SuccessorTree.V10

/-- Strict raw prefix implies strict increase of socle length. -/
theorem rawPartialType_level_lt_of_lt
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : a < b) :
    a.1 < b.1 := by
  have hle : a.1 ≤ b.1 :=
    rawPartialTypePrefix_level_le hab.le
  by_contra hn
  have heqLevel : a.1 = b.1 := by omega
  have heq : a = b :=
    rawPartialTypePrefix_eq_of_same_level hab.le heqLevel
  exact hab.ne heq

/-- A cover in the raw prefix forest has exactly one more socle
coordinate. If the levels differed by two, the canonical
intermediate full L+ prefix would contradict the cover relation. -/
theorem rawPartialType_covBy_level
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : a ⋖ b) :
    b.1 = a.1 + 1 := by
  have hlt : a.1 < b.1 :=
    rawPartialType_level_lt_of_lt hab.lt
  by_contra hne
  have hgap : a.1 + 1 < b.1 := by omega
  let z := rawPartialTypeAncestor b (a.1 + 1) (by omega)
  have hzb : z ≤ b :=
    rawPartialTypeAncestor_le b (a.1 + 1) (by omega)
  have haz : a ≤ z := by
    rcases rawPartialType_lower_linear hab.le hzb with h | h
    · exact h
    · have hlevels := rawPartialTypePrefix_level_le h
      change a.1 + 1 ≤ a.1 at hlevels
      omega
  have hazStrict : a < z := by
    refine lt_of_le_of_ne haz ?_
    intro heq
    have hlevel := congrArg Sigma.fst heq
    change a.1 = a.1 + 1 at hlevel
    omega
  have hzbStrict : z < b := by
    refine lt_of_le_of_ne hzb ?_
    intro heq
    have hlevel := congrArg Sigma.fst heq
    change a.1 + 1 = b.1 at hlevel
    omega
  exact (not_covBy_of_lt_of_lt hazStrict hzbStrict) hab

/-- The abstract LevelTree axioms now follow without adding a
tree/meet field to the definition of a partial type. -/
noncomputable instance instRawPartialTypeLevelTree
    (db du dd : Nat) :
    LevelTree (RawPartialTypeNode db du dd) where
  level := Sigma.fst
  level_lt := rawPartialType_level_lt_of_lt
  covBy_level := rawPartialType_covBy_level
  lower_linear := by
    intro a b c hac hbc
    exact rawPartialType_lower_linear hac hbc
  ancestor_exists := by
    intro a n hn
    exact rawPartialType_ancestor_exists a n hn
  level_finite := rawPartialTypeLevel_finite db du dd
  meet := rawMeet
  meet_le_left := by
    intro a b hcommon
    exact rawMeet_le_left a b hcommon
  meet_le_right := by
    intro a b hcommon
    exact rawMeet_le_right a b hcommon
  le_meet := by
    intro a b c hca hcb
    exact raw_le_meet hca hcb

/-- The actual LevelTree meet is definitionally the constructed
maximal raw full-type prefix, not a second chosen operation. -/
theorem rawLevelTree_meet_eq
    {db du dd : Nat}
    (a b : RawPartialTypeNode db du dd) :
    LevelTree.meet a b = rawMeet a b := rfl

/-- In the raw LevelTree the unique ancestor at any shorter level
is precisely the explicit full L+ restriction. -/
theorem rawLevelTree_ancestor_eq_restrict
    {db du dd : Nat}
    (a : RawPartialTypeNode db du dd)
    (n : Nat) (hn : n ≤ LevelTree.lev a) :
    LevelTree.ancestor a n hn =
      rawPartialTypeAncestor a n (by
        simpa only [LevelTree.lev, instRawPartialTypeLevelTree] using hn) := by
  have hRawLevel : n ≤ a.1 := hn
  have hRawAnc : rawPartialTypeAncestor a n hRawLevel ≤ a :=
    rawPartialTypeAncestor_le a n hRawLevel
  have hLev : LevelTree.lev
      (rawPartialTypeAncestor a n hRawLevel) = n := rfl
  exact (LevelTree.eq_ancestor_of_le hRawAnc hLev hn).symm

end SuccessorTree.V10
