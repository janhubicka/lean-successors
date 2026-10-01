import SuccessorTree.ShapePreserving
import Mathlib.Tactic

/-!
# (S,M)-trees

Definition 1.5 from the successor-tree paper.  The monoid is represented by a
predicate on shape-preserving maps together with witnesses for M1--M3.
-/

namespace SuccessorTree

variable {Node : Type u} {Char : Type v} [PartialOrder Node]

def AgreesThrough
    (S : STree Node Char)
    (F G : ShapeMap S) (n : Nat) : Prop :=
  ∀ a : Node, S.tree.level a ≤ n → F a = G a

structure SMTree (S : STree Node Char) where
  mem : ShapeMap S → Prop

  -- M1: closed monoid
  id_mem : mem (ShapeMap.id S)
  comp_mem :
    ∀ {F G : ShapeMap S}, mem F → mem G → mem (F.comp G)
  limit_mem :
    ∀ (F : Nat → ShapeMap S),
      (∀ i, mem (F i)) →
      (∀ i, AgreesThrough S (F i) (F (i + 1)) i) →
      ∃ F∞ : ShapeMap S,
        mem F∞ ∧ ∀ i, AgreesThrough S F∞ (F i) i

  -- M2: one-level decomposition.
  decompose :
    ∀ (n : Nat) (F : ShapeMap S),
      mem F →
      0 < F.levelMap n →
      F.SkipsLevel (F.levelMap n - 1) →
      ∃ F1 F2 : ShapeMap S,
        mem F1 ∧
        mem F2 ∧
        F1.levelMap n = F.levelMap n - 1 ∧
        F2.SkipsOnlyLevel (F.levelMap n - 1) ∧
        (∀ a : Node, F2 (F1 a) = F a)

  -- M3: duplication.  The chosen map F_m^n skips only level m and copies,
  -- at level m, the successor data seen at level n.
  duplicate :
    ∀ (n m : Nat), n < m → ShapeMap S
  duplicate_mem :
    ∀ (n m : Nat) (h : n < m), mem (duplicate n m h)
  duplicate_skips_only :
    ∀ (n m : Nat) (h : n < m),
      (duplicate n m h).SkipsOnlyLevel m
  duplicate_rule :
    ∀ (n m : Nat) (h : n < m)
      {a b x : Node} {ps : List Node} {c : Char},
      S.tree.level a = n →
      S.tree.level b = m →
      S.succ a ps c = some x →
      x ≤ b →
      ∃ y : Node,
        S.succ b ps c = some y ∧
        duplicate n m h b = y

namespace SMTree

def Contains (M : SMTree S) (F : ShapeMap S) : Prop :=
  M.mem F

theorem id_contains (M : SMTree S) :
    M.Contains (ShapeMap.id S) :=
  M.id_mem

theorem comp_contains
    (M : SMTree S) {F G : ShapeMap S}
    (hF : M.Contains F) (hG : M.Contains G) :
    M.Contains (F.comp G) :=
  M.comp_mem hF hG

/-- Convenient functional form of M3. -/
theorem duplicate_succ
    (M : SMTree S)
    (n m : Nat) (h : n < m)
    {a b x : Node} {ps : List Node} {c : Char}
    (ha : S.tree.level a = n)
    (hb : S.tree.level b = m)
    (hs : S.succ a ps c = some x)
    (hxb : x ≤ b) :
    ∃ y : Node,
      S.succ b ps c = some y ∧
      M.duplicate n m h b = y :=
  M.duplicate_rule n m h ha hb hs hxb

end SMTree

end SuccessorTree
