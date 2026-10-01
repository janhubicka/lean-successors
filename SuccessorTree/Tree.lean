import Mathlib.Order.Cover
import Mathlib.Data.Set.Finite.Basic

/-!
# Levelled trees used by the successor-tree formalization

This is the structural interface used to formalize the paper before the first
pigeonhole lemma.

The paper defines the level of a node as the number of strict predecessors.
For the paper's (possibly empty, not necessarily pruned) trees, the
fields below are elementary consequences of that definition:

* levels strictly increase along the tree order;
* an immediate successor raises the level by one;
* predecessors of a common node are comparable;
* every level is finite;
* nodes with a common predecessor have the greatest common predecessor (meet)
  used in the paper.

Keeping these consequences explicit makes dependencies in later proofs easy
to audit.  A separate representation-equivalence lemma can later connect this
interface to the paper's set-theoretic definition verbatim.
-/

namespace SuccessorTree

/-- The order/level facts about the paper's tree definition which are used by
the successor machinery. No nonemptiness or pruning assumption is built in. -/
class LevelTree (T : Type u) [PartialOrder T] where
  level : T → Nat
  level_lt : ∀ {a b : T}, a < b → level a < level b
  covBy_level : ∀ {a b : T}, a ⋖ b → level b = level a + 1
  lower_linear : ∀ {a b c : T}, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a
  /-- Every lower level occurs on the predecessor chain of a node. -/
  ancestor_exists : ∀ (a : T) (n : Nat), n ≤ level a →
    ∃ b : T, b ≤ a ∧ level b = n
  level_finite : ∀ n : Nat, Set.Finite {a : T | level a = n}
  /-- Greatest common predecessor; the laws below are required only when a
  common predecessor exists.  This is the paper's meet operation. -/
  meet : T → T → T
  meet_le_left : ∀ {a b : T}, (∃ c : T, c ≤ a ∧ c ≤ b) → meet a b ≤ a
  meet_le_right : ∀ {a b : T}, (∃ c : T, c ≤ a ∧ c ≤ b) → meet a b ≤ b
  le_meet : ∀ {a b c : T}, c ≤ a → c ≤ b → c ≤ meet a b

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

/-- Two distinct immediate-successor cones above `x` have meet exactly
`x`.  This is the order-theoretic step used in the paper's meet-preservation
argument. -/
theorem meet_le_of_distinct_covBy
    {x s t a b : T}
    (hxs : x ⋖ s) (hxt : x ⋖ t) (hst : s ≠ t)
    (hsa : s ≤ a) (htb : t ≤ b) :
    LevelTree.meet a b ≤ x := by
  have hxa : x ≤ a := hxs.le.trans hsa
  have hxb : x ≤ b := hxt.le.trans htb
  have hcommon : ∃ c : T, c ≤ a ∧ c ≤ b := ⟨x, hxa, hxb⟩
  have hma : LevelTree.meet a b ≤ a := LevelTree.meet_le_left hcommon
  have hmb : LevelTree.meet a b ≤ b := LevelTree.meet_le_right hcommon
  have hxm : x ≤ LevelTree.meet a b := LevelTree.le_meet hxa hxb
  rcases hxm.eq_or_lt with hEq | hxm'
  · simpa [hEq]
  · have hsm : s ≤ LevelTree.meet a b := by
      rcases comparable_below hsa hma with h | h
      · exact h
      · rcases h.eq_or_lt with hEq | hlt
        · simpa [hEq]
        · exact False.elim ((not_covBy_of_lt_of_lt hxm' hlt) hxs)
    have htm : t ≤ LevelTree.meet a b := by
      rcases comparable_below htb hmb with h | h
      · exact h
      · rcases h.eq_or_lt with hEq | hlt
        · simpa [hEq]
        · exact False.elim ((not_covBy_of_lt_of_lt hxm' hlt) hxt)
    rcases comparable_below hsm htm with hstle | htsle
    · have heq : s = t := same_level_of_le hstle (by
        rw [covBy_level_eq hxs, covBy_level_eq hxt])
      exact False.elim (hst heq)
    · have heq : t = s := same_level_of_le htsle (by
        rw [covBy_level_eq hxt, covBy_level_eq hxs])
      exact False.elim (hst heq.symm)

end LevelTree

end SuccessorTree
