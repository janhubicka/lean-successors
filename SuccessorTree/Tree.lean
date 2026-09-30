import Mathlib.Order.Cover
import Mathlib.Data.Set.Finite.Basic

/-!
# Levelled trees used by the successor-tree formalization

This is the structural interface used to formalize the paper before the first
pigeonhole lemma.

The paper defines the level of a node as the number of strict predecessors.
For a nonempty pruned finitely-branching tree with finitely many roots, the
fields below are elementary consequences of that definition:

* levels strictly increase along the tree order;
* an immediate successor raises the level by one;
* predecessors of a common node are comparable;
* every level is finite and nonempty;
* every node has an immediate successor.

Keeping these consequences explicit makes dependencies in later proofs easy
to audit.  A separate representation-equivalence lemma can later connect this
interface to the paper's set-theoretic definition verbatim.
-/

namespace SuccessorTree

/-- The order/level facts about the paper's corrected (nonempty, pruned) tree
definition which are used by the successor machinery. -/
class LevelTree (T : Type u) [PartialOrder T] where
  level : T → Nat
  level_lt : ∀ {a b : T}, a < b → level a < level b
  covBy_level : ∀ {a b : T}, a ⋖ b → level b = level a + 1
  lower_linear : ∀ {a b c : T}, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a
  /-- Every lower level occurs on the predecessor chain of a node. -/
  ancestor_exists : ∀ (a : T) (n : Nat), n ≤ level a →
    ∃ b : T, b ≤ a ∧ level b = n
  level_finite : ∀ n : Nat, Set.Finite {a : T | level a = n}
  level_nonempty : ∀ n : Nat, ∃ a : T, level a = n
  pruned : ∀ a : T, ∃ b : T, a ⋖ b

namespace LevelTree

variable {T : Type u} [PartialOrder T] [LevelTree T]

/-- Paper notation \(\ell(a)\). -/
abbrev lev (a : T) : Nat := LevelTree.level a

theorem lt_level_lt {a b : T} (h : a < b) : lev a < lev b :=
  LevelTree.level_lt h

theorem level_le_of_le {a b : T} (h : a ≤ b) : lev a ≤ lev b := by
  rcases h.eq_or_lt with h | h
  · simpa [h]
  · exact Nat.le_of_lt (lt_level_lt h)

theorem covBy_level_eq {a b : T} (h : a ⋖ b) :
    lev b = lev a + 1 :=
  LevelTree.covBy_level h

theorem same_level_of_le {a b : T} (hab : a ≤ b)
    (hlev : lev a = lev b) : a = b := by
  rcases hab.eq_or_lt with h | h
  · exact h
  · exact False.elim ((Nat.ne_of_lt (lt_level_lt h)) hlev)

theorem comparable_below {a b c : T} (ha : a ≤ c) (hb : b ≤ c) :
    a ≤ b ∨ b ≤ a :=
  LevelTree.lower_linear ha hb

/-- The predecessor of `a` on level `n`. -/
noncomputable def ancestor (a : T) (n : Nat) (h : n ≤ lev a) : T :=
  Classical.choose (LevelTree.ancestor_exists a n h)

theorem ancestor_le (a : T) (n : Nat) (h : n ≤ lev a) :
    ancestor a n h ≤ a :=
  (Classical.choose_spec (LevelTree.ancestor_exists a n h)).1

theorem level_ancestor (a : T) (n : Nat) (h : n ≤ lev a) :
    lev (ancestor a n h) = n :=
  (Classical.choose_spec (LevelTree.ancestor_exists a n h)).2

/-- A predecessor at a prescribed level is unique. -/
theorem eq_ancestor_of_le {a b : T} (hba : b ≤ a)
    (hlev : lev b = n) (hn : n ≤ lev a) :
    b = ancestor a n hn := by
  have hanc := ancestor_le a n hn
  rcases comparable_below hba hanc with h | h
  · exact same_level_of_le h (hlev.trans (level_ancestor a n hn).symm)
  · exact (same_level_of_le h ((level_ancestor a n hn).trans hlev.symm)).symm

/-- Comparable nodes on consecutive levels form a cover. -/
theorem covBy_of_le_level_succ {a b : T} (hab : a ≤ b)
    (hlev : lev b = lev a + 1) : a ⋖ b := by
  refine ⟨?_, ?_⟩
  · exact lt_of_le_of_ne hab (fun h => by
      subst h
      omega)
  · intro c hac hcb
    have h1 := lt_level_lt hac
    have h2 := lt_level_lt hcb
    omega

/-- The next ancestor above a strict predecessor is an immediate successor. -/
theorem exists_covBy_between {a b : T} (hab : a < b) :
    ∃ c : T, a ⋖ c ∧ c ≤ b := by
  have hlevel : lev a + 1 ≤ lev b := by
    exact Nat.succ_le_iff.mpr (lt_level_lt hab)
  let c := ancestor b (lev a + 1) hlevel
  have hcb : c ≤ b := ancestor_le b (lev a + 1) hlevel
  have hac : a ≤ c := by
    rcases comparable_below hab.le hcb with h | h
    · exact h
    · have hl := level_le_of_le h
      have hc : lev c = lev a + 1 := by
        simp [c, level_ancestor]
      omega
  refine ⟨c, covBy_of_le_level_succ hac ?_, hcb⟩
  simp [c, level_ancestor]

theorem exists_immediateSuccessor (a : T) : ∃ b : T, a ⋖ b :=
  LevelTree.pruned a

end LevelTree

end SuccessorTree
