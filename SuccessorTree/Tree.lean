import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Levelled trees

A structural core for the successor-tree theorem.  We record the unique
predecessor at each lower level directly; this is equivalent to the paper's
definition that every predecessor set is finite and linearly ordered.
-/

namespace SuccessorTree

structure LevelTree (Node : Type u) [PartialOrder Node] where
  level : Node → Nat
  level_strict : ∀ {a b : Node}, a < b → level a < level b
  predecessor_exists :
    ∀ (a : Node) (m : Nat), m < level a →
      ∃ b : Node, b < a ∧ level b = m
  predecessor_unique :
    ∀ {a b c : Node}, b < a → c < a → level b = level c → b = c
  roots_finite : Set.Finite {a : Node | level a = 0}
  immediate_finite :
    ∀ a : Node, Set.Finite {b : Node | a < b ∧ level b = level a + 1}

namespace LevelTree

def IsRoot (T : LevelTree Node) (a : Node) : Prop :=
  T.level a = 0

def IsImmediateSuccessor (T : LevelTree Node) (a b : Node) : Prop :=
  a < b ∧ T.level b = T.level a + 1

theorem level_le_of_le (T : LevelTree Node) {a b : Node} (h : a ≤ b) :
    T.level a ≤ T.level b := by
  rcases h.eq_or_lt with hEq | hlt
  · subst b
    exact le_rfl
  · exact Nat.le_of_lt (T.level_strict hlt)

theorem eq_of_le_of_level_eq
    (T : LevelTree Node) {a b : Node}
    (h : a ≤ b) (hl : T.level a = T.level b) :
    a = b := by
  rcases h.eq_or_lt with hEq | hlt
  · exact hEq
  · have hlevels := T.level_strict hlt
    omega

theorem predecessor_at_level_unique
    (T : LevelTree Node) {a b c : Node}
    (hb : b < a) (hc : c < a)
    (hbl : T.level b = m) (hcl : T.level c = m) :
    b = c :=
  T.predecessor_unique hb hc (hbl.trans hcl.symm)

theorem predecessor_le
    (T : LevelTree Node) {a b c : Node}
    (ha : a < c) (hb : b < c)
    (hlab : T.level a ≤ T.level b) :
    a ≤ b := by
  by_cases hEq : T.level a = T.level b
  · exact (T.predecessor_unique ha hb hEq).le
  · have hlt : T.level a < T.level b := lt_of_le_of_ne hlab hEq
    obtain ⟨d, hdb, hdlevel⟩ :=
      T.predecessor_exists b (T.level a) hlt
    have hdc : d < c := lt_trans hdb hb
    have hda : d = a :=
      T.predecessor_unique hdc ha hdlevel
    subst d
    exact hdb.le

theorem predecessor_of_succ_level
    (T : LevelTree Node) {a b : Node}
    (hab : a < b)
    (hlevel : T.level b = T.level a + 1) :
    T.IsImmediateSuccessor a b :=
  ⟨hab, hlevel⟩

theorem exists_immediate_predecessor
    (T : LevelTree Node) (b : Node) (hpos : 0 < T.level b) :
    ∃ a : Node, T.IsImmediateSuccessor a b := by
  obtain ⟨a, hab, halevel⟩ :=
    T.predecessor_exists b (T.level b - 1) (by omega)
  refine ⟨a, hab, ?_⟩
  omega

end LevelTree

end SuccessorTree
