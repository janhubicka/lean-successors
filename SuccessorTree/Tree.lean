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
  level_finite : ∀ n : Nat, Set.Finite {a : T | level a = n}
  level_nonempty : ∀ n : Nat, ∃ a : T, level a = n
  pruned : ∀ a : T, ∃ b : T, a ⋖ b

namespace LevelTree

variable {T : Type u} [PartialOrder T] [LevelTree T]

/-- Paper notation \(\ell(a)\). -/
abbrev lev (a : T) : Nat := LevelTree.level a

theorem lt_level_lt {a b : T} (h : a < b) : lev a < lev b :=
  LevelTree.level_lt h

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

theorem exists_immediateSuccessor (a : T) : ∃ b : T, a ⋖ b :=
  LevelTree.pruned a

end LevelTree

end SuccessorTree
