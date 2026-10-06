import SuccessorTree.EnvelopePullback
import Mathlib.Tactic

/-!
# Local structural lemmas for the envelope algorithm

These lemmas formalize the two "well-defined" steps used before the recursive
construction: finiteness of the closure and uniqueness of the next prefix when
there is no meet at the current level.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Nodes of level at most `N` form a finite set. -/
def levelLe (N : Nat) : Set T := {x | LevelTree.lev x ≤ N}

theorem levelLe_finite (N : Nat) : (levelLe (T := T) N).Finite := by
  induction N with
  | zero =>
      simpa [levelLe, Nat.le_zero] using (LevelTree.level_finite (T := T) 0)
  | succ N ih =>
      have hEq :
          levelLe (T := T) (N + 1) =
            levelLe (T := T) N ∪ {x : T | LevelTree.lev x = N + 1} := by
        ext x
        simp only [levelLe, Set.mem_setOf_eq, Set.mem_union]
        omega
      rw [hEq]
      exact ih.union (LevelTree.level_finite (T := T) (N + 1))

theorem levelLe_meetClosed (N : Nat) :
    MeetClosed (levelLe (T := T) N) := by
  intro a b ha hb hab
  change LevelTree.lev (LevelTree.meet a b) ≤ N
  exact (LevelTree.level_le_of_le (LevelTree.meet_le_left hab)).trans ha

theorem levelLe_parameterClosed (N : Nat) (I : Set Nat) :
    ParameterClosedOver S (levelLe (T := T) N) I := by
  intro a ha i hi hia p c hs x hx
  change LevelTree.lev x ≤ N
  have hxi := S.parameter_level_lt hs hx
  have hbase :=
    LevelTree.level_ancestor a i (Nat.le_of_lt hia)
  rw [hbase] at hxi
  omega

/-- Closure never creates nodes above the original level bound. -/
theorem closure_subset_levelLe
    (I : Set Nat) (X : Set T) (N : Nat)
    (hX : X ⊆ levelLe (T := T) N) :
    closure S I X ⊆ levelLe (T := T) N := by
  exact closure_minimal S I X (levelLe (T := T) N) hX
    (levelLe_meetClosed N) (levelLe_parameterClosed N I)

/-- In particular the closure of a bounded set is finite. -/
theorem closure_finite_of_bounded
    (I : Set Nat) (X : Set T) (N : Nat)
    (hX : X ⊆ levelLe (T := T) N) :
    (closure S I X).Finite :=
  (levelLe_finite N).subset (closure_subset_levelLe I X N hX)

/-- If two nodes have the same prefix at level `i`, but different prefixes at
level `i+1`, then their meet has level exactly `i`. -/
theorem meet_level_eq_of_nextPrefix_ne
    {a b : T} {i : Nat}
    (hia : i < LevelTree.lev a) (hib : i < LevelTree.lev b)
    (hi :
      LevelTree.ancestor a i (Nat.le_of_lt hia) =
        LevelTree.ancestor b i (Nat.le_of_lt hib))
    (hne :
      LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hia) ≠
        LevelTree.ancestor b (i + 1) (Nat.succ_le_iff.mpr hib)) :
    LevelTree.lev (LevelTree.meet a b) = i := by
  let r := LevelTree.ancestor a i (Nat.le_of_lt hia)
  let sa := LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hia)
  let sb := LevelTree.ancestor b (i + 1) (Nat.succ_le_iff.mpr hib)
  have hra : r ≤ a := LevelTree.ancestor_le a i (Nat.le_of_lt hia)
  have hsa : sa ≤ a :=
    LevelTree.ancestor_le a (i + 1) (Nat.succ_le_iff.mpr hia)
  have hrb0 :
      LevelTree.ancestor b i (Nat.le_of_lt hib) ≤ b :=
    LevelTree.ancestor_le b i (Nat.le_of_lt hib)
  have hrb : r ≤ b := by
    dsimp [r]
    rw [hi]
    exact hrb0
  have hsb : sb ≤ b :=
    LevelTree.ancestor_le b (i + 1) (Nat.succ_le_iff.mpr hib)
  have hrlev : LevelTree.lev r = i :=
    LevelTree.level_ancestor a i (Nat.le_of_lt hia)
  have hsalev : LevelTree.lev sa = i + 1 :=
    LevelTree.level_ancestor a (i + 1) (Nat.succ_le_iff.mpr hia)
  have hsblev : LevelTree.lev sb = i + 1 :=
    LevelTree.level_ancestor b (i + 1) (Nat.succ_le_iff.mpr hib)
  have hrsa : r ⋖ sa := by
    apply LevelTree.covBy_of_le_level_succ
    · rcases LevelTree.comparable_below hra hsa with h | h
      · exact h
      · have hlev := LevelTree.level_le_of_le h
        omega
    · omega
  have hrsb : r ⋖ sb := by
    apply LevelTree.covBy_of_le_level_succ
    · rcases LevelTree.comparable_below hrb hsb with h | h
      · exact h
      · have hlev := LevelTree.level_le_of_le h
        omega
    · omega
  have hmeet_le : LevelTree.meet a b ≤ r :=
    LevelTree.meet_le_of_distinct_covBy hrsa hrsb (by simpa [sa, sb] using hne) hsa hsb
  have hr_meet : r ≤ LevelTree.meet a b :=
    LevelTree.le_meet hra hrb
  have heq : LevelTree.meet a b = r := le_antisymm hmeet_le hr_meet
  rw [heq, hrlev]

/-- Consequently, absence of a meet on level `i` makes the map
`a|_i ↦ a|_{i+1}` well-defined on any family of nodes above `i`. -/
theorem nextPrefix_eq_of_no_meet
    {a b : T} {i : Nat}
    (hia : i < LevelTree.lev a) (hib : i < LevelTree.lev b)
    (hi :
      LevelTree.ancestor a i (Nat.le_of_lt hia) =
        LevelTree.ancestor b i (Nat.le_of_lt hib))
    (hno : LevelTree.lev (LevelTree.meet a b) ≠ i) :
    LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hia) =
      LevelTree.ancestor b (i + 1) (Nat.succ_le_iff.mpr hib) := by
  by_contra hne
  exact hno (meet_level_eq_of_nextPrefix_ne hia hib hi hne)

end Envelope
end SMTree
end SuccessorTree
