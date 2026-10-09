import SuccessorTree.Tree
import Mathlib.Tactic

/-!
# From a first distinct prefix to a meet

The v10 trace theorem identifies the first numerical coordinate at which
two complete binary records differ. These elementary LevelTree lemmas prove
that, once equality of records is transferred to equality of ancestors,
a first distinction at the *next* source level determines the meet.

This is a general forest theorem, with no H-construction or Ramsey axioms.
Proving that the full partial-type records, including E-socles, induce these
ancestor equalities is deliberately a separate adapter obligation.
-/

namespace SuccessorTree.V10

universe u
variable {T : Type u} [PartialOrder T] [LevelTree T]

/-- A common prefix at level d, followed by distinct next prefixes,
has meet exactly at level d. -/
theorem meet_eq_of_adjacent_ancestors
    (a b : T) (d : Nat)
    (hda : d ≤ LevelTree.lev a)
    (hdb : d ≤ LevelTree.lev b)
    (ha : d + 1 ≤ LevelTree.lev a)
    (hb : d + 1 ≤ LevelTree.lev b)
    (hcommon :
      LevelTree.ancestor a d hda = LevelTree.ancestor b d hdb)
    (hdiff :
      LevelTree.ancestor a (d + 1) ha ≠
        LevelTree.ancestor b (d + 1) hb) :
    LevelTree.meet a b = LevelTree.ancestor a d hda := by
  let x := LevelTree.ancestor a d hda
  have hxA : x ≤ a := LevelTree.ancestor_le a d hda
  have hxB : x ≤ b := by
    change LevelTree.ancestor a d hda ≤ b
    rw [hcommon]
    exact LevelTree.ancestor_le b d hdb
  have hab : ∃ c : T, c ≤ a ∧ c ≤ b := ⟨x, hxA, hxB⟩
  have hxM : x ≤ LevelTree.meet a b :=
    LevelTree.le_meet hxA hxB
  apply le_antisymm ?_ hxM
  by_contra hnot
  have hneq : x ≠ LevelTree.meet a b := by
    intro heq
    apply hnot
    simpa [heq]
  have hlt : x < LevelTree.meet a b := lt_of_le_of_ne hxM hneq
  have hlevel : d + 1 ≤ LevelTree.lev (LevelTree.meet a b) := by
    have hxlev : LevelTree.lev x = d := LevelTree.level_ancestor a d hda
    have hstrict := LevelTree.lt_level_lt hlt
    omega
  let z := LevelTree.ancestor (LevelTree.meet a b) (d + 1) hlevel
  have hzlev : LevelTree.lev z = d + 1 :=
    LevelTree.level_ancestor (LevelTree.meet a b) (d + 1) hlevel
  have hzA : z ≤ a :=
    (LevelTree.ancestor_le (LevelTree.meet a b) (d + 1) hlevel).trans
      (LevelTree.meet_le_left hab)
  have hzB : z ≤ b :=
    (LevelTree.ancestor_le (LevelTree.meet a b) (d + 1) hlevel).trans
      (LevelTree.meet_le_right hab)
  have hza : z = LevelTree.ancestor a (d + 1) ha :=
    LevelTree.eq_ancestor_of_le hzA hzlev ha
  have hzb : z = LevelTree.ancestor b (d + 1) hb :=
    LevelTree.eq_ancestor_of_le hzB hzlev hb
  exact hdiff (hza.symm.trans hzb)

/-- The level formulation needed for the proposed v10 charge. -/
theorem meet_level_of_adjacent_ancestors
    (a b : T) (d : Nat)
    (hda : d ≤ LevelTree.lev a)
    (hdb : d ≤ LevelTree.lev b)
    (ha : d + 1 ≤ LevelTree.lev a)
    (hb : d + 1 ≤ LevelTree.lev b)
    (hcommon :
      LevelTree.ancestor a d hda = LevelTree.ancestor b d hdb)
    (hdiff :
      LevelTree.ancestor a (d + 1) ha ≠
        LevelTree.ancestor b (d + 1) hb) :
    LevelTree.lev (LevelTree.meet a b) = d := by
  rw [meet_eq_of_adjacent_ancestors a b d hda hdb ha hb hcommon hdiff]
  exact LevelTree.level_ancestor a d hda

end SuccessorTree.V10
