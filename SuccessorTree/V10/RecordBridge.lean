import SuccessorTree.V10.AncestorMeet
import Mathlib.Tactic

/-!
# Record-prefix comparison and meets

A complete partial-type record consists of its E-socle, its initial
L-structure, and all relations from the distinguished type vertex. The
specific coding of those records by a sequence is still to be constructed.

This abstract lemma isolates exactly the two requirements on that coding:
equal records through d determine equal d-th ancestors; equal (d+1)-st
ancestors determine equality of the record at d. The first record
disagreement can then be converted to the genuine LevelTree meet.

This is a proved consequence of the assumptions; it does not claim that
the manuscript's full partial-type model already satisfies them.
-/

namespace SuccessorTree.V10

universe u v
variable {T : Type u} [PartialOrder T] [LevelTree T]
variable {Record : Type v}

/-- Two adjacent prefix-reflection properties are sufficient to recover
the meet from a first difference of complete type records. -/
theorem meet_of_first_record_difference
    (code : T → Nat → Record) (a b : T) (d : Nat)
    (ha : d + 1 ≤ LevelTree.lev a)
    (hb : d + 1 ≤ LevelTree.lev b)
    (hprefix :
      (∀ q < d, code a q = code b q) →
        LevelTree.ancestor a d (by omega) =
          LevelTree.ancestor b d (by omega))
    (hreflect :
      LevelTree.ancestor a (d + 1) ha =
        LevelTree.ancestor b (d + 1) hb →
      code a d = code b d)
    (hagree : ∀ q < d, code a q = code b q)
    (hdiff : code a d ≠ code b d) :
    LevelTree.meet a b = LevelTree.ancestor a d (by omega) := by
  have hcommon := hprefix hagree
  have hnext :
      LevelTree.ancestor a (d + 1) ha ≠
        LevelTree.ancestor b (d + 1) hb := by
    intro h
    exact hdiff (hreflect h)
  exact meet_eq_of_adjacent_ancestors a b d
    (by omega) (by omega) ha hb hcommon hnext

/-- The associated generation/level statement, once the complete records
are known to reflect predecessor equality. -/
theorem meet_level_of_first_record_difference
    (code : T → Nat → Record) (a b : T) (d : Nat)
    (ha : d + 1 ≤ LevelTree.lev a)
    (hb : d + 1 ≤ LevelTree.lev b)
    (hprefix :
      (∀ q < d, code a q = code b q) →
        LevelTree.ancestor a d (by omega) =
          LevelTree.ancestor b d (by omega))
    (hreflect :
      LevelTree.ancestor a (d + 1) ha =
        LevelTree.ancestor b (d + 1) hb →
      code a d = code b d)
    (hagree : ∀ q < d, code a q = code b q)
    (hdiff : code a d ≠ code b d) :
    LevelTree.lev (LevelTree.meet a b) = d := by
  rw [meet_of_first_record_difference code a b d ha hb
    hprefix hreflect hagree hdiff]
  exact LevelTree.level_ancestor a d (by omega)

end SuccessorTree.V10
