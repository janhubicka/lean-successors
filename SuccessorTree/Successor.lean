import SuccessorTree.Tree
import Mathlib.Data.List.Basic

/-!
# Trees with a successor operation

Definition 1.1 of the successor-tree paper.  Undefined successor terms are
represented by `none`.
-/

namespace SuccessorTree

structure STree (Node : Type u) (Char : Type v)
    [PartialOrder Node] where
  tree : LevelTree Node
  succ : Node → List Node → Char → Option Node

  -- S1
  succ_immediate :
    ∀ {a b : Node} {ps : List Node} {c : Char},
      succ a ps c = some b →
        tree.IsImmediateSuccessor a b
  parameter_below :
    ∀ {a b : Node} {ps : List Node} {c : Char},
      succ a ps c = some b →
        ∀ p ∈ ps, tree.level p < tree.level a

  -- S2
  succ_injective :
    ∀ {a b x : Node} {ps qs : List Node} {c d : Char},
      succ a ps c = some x →
      succ b qs d = some x →
        a = b ∧ ps = qs ∧ c = d

  -- S3
  succ_constructive :
    ∀ {a b : Node},
      tree.IsImmediateSuccessor a b →
        ∃ ps : List Node, ∃ c : Char, succ a ps c = some b

namespace STree

variable {Node : Type u} {Char : Type v} [PartialOrder Node]

def Defined (S : STree Node Char) (a : Node) (ps : List Node) (c : Char) : Prop :=
  ∃ b, S.succ a ps c = some b

theorem succ_level
    (S : STree Node Char)
    {a b : Node} {ps : List Node} {c : Char}
    (h : S.succ a ps c = some b) :
    S.tree.level b = S.tree.level a + 1 :=
  (S.succ_immediate h).2

theorem succ_base_lt
    (S : STree Node Char)
    {a b : Node} {ps : List Node} {c : Char}
    (h : S.succ a ps c = some b) :
    a < b :=
  (S.succ_immediate h).1

theorem succ_data_unique
    (S : STree Node Char)
    {a b x : Node} {ps qs : List Node} {c d : Char}
    (h1 : S.succ a ps c = some x)
    (h2 : S.succ b qs d = some x) :
    a = b ∧ ps = qs ∧ c = d :=
  S.succ_injective h1 h2

end STree

end SuccessorTree
