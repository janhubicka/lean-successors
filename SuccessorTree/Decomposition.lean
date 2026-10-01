import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Successor decompositions

For a non-root node x, S3 gives a presentation x = S(a,ps,c), and S2 makes
(a,ps,c) unique.  This packages the paper's Db/Dp/Dc notation.
-/

namespace SuccessorTree

variable {Node : Type u} {Char : Type v} [PartialOrder Node]

structure SuccData (S : STree Node Char) (x : Node) where
  base : Node
  params : List Node
  char : Char
  eq_succ : S.succ base params char = some x

namespace STree

noncomputable def succDataOfNonroot
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x) :
    SuccData S x := by
  classical
  obtain ⟨a, ha⟩ := S.tree.exists_immediate_predecessor x hx
  obtain ⟨ps, c, hsucc⟩ := S.succ_constructive ha
  exact ⟨a, ps, c, hsucc⟩

theorem succData_unique
    (S : STree Node Char) (x : Node)
    (D E : SuccData S x) :
    D.base = E.base ∧ D.params = E.params ∧ D.char = E.char := by
  exact S.succ_injective D.eq_succ E.eq_succ

noncomputable def Db
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x) : Node :=
  (S.succDataOfNonroot x hx).base

noncomputable def Dp
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x) : List Node :=
  (S.succDataOfNonroot x hx).params

noncomputable def Dc
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x) : Char :=
  (S.succDataOfNonroot x hx).char

theorem decompose_nonroot
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x) :
    S.succ (S.Db x hx) (S.Dp x hx) (S.Dc x hx) = some x :=
  (S.succDataOfNonroot x hx).eq_succ

theorem Db_level
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x) :
    S.tree.level (S.Db x hx) + 1 = S.tree.level x := by
  have h := S.succ_level (S.decompose_nonroot x hx)
  omega

theorem Dp_below
    (S : STree Node Char) (x : Node)
    (hx : 0 < S.tree.level x)
    {p : Node} (hp : p ∈ S.Dp x hx) :
    S.tree.level p < S.tree.level (S.Db x hx) := by
  exact S.parameter_below (S.decompose_nonroot x hx) p hp

theorem decomposition_eq
    (S : STree Node Char)
    {a x : Node} {ps : List Node} {c : Char}
    (h : S.succ a ps c = some x)
    (hx : 0 < S.tree.level x) :
    S.Db x hx = a ∧ S.Dp x hx = ps ∧ S.Dc x hx = c := by
  let D := S.succDataOfNonroot x hx
  have hu := S.succ_injective D.eq_succ h
  exact hu

end STree

end SuccessorTree
