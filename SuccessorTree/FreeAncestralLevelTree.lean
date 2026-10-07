import SuccessorTree.FreeAncestralOrder
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! # LevelTree instance for free ancestral histories

The meet is chosen as the common prefix of greatest level. Rootedness ensures
that level zero is always common, while comparability of prefixes makes the
greatest common prefix unique.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}

/-- The formal root node. -/
def rootNode : Node Label arity :=
  ⟨0, History.root⟩

theorem root_le (x : Node Label arity) :
    rootNode ≤ x := by
  rcases x with ⟨n, h⟩
  obtain ⟨a, ha⟩ :=
    Prefix.exists_at_level h 0 (Nat.zero_le n)
  have ha0 : a = History.root :=
    history_zero_unique a
  subst a
  exact ha

/-- There is a common predecessor of x,y on level k. -/
def CommonLevel (x y : Node Label arity) (k : Nat) : Prop :=
  ∃ z : Node Label arity,
    z ≤ x ∧ z ≤ y ∧ z.level = k

theorem commonLevel_zero (x y : Node Label arity) :
    CommonLevel x y 0 :=
  ⟨rootNode, root_le x, root_le y, rfl⟩

/-- Greatest level on which x,y have a common prefix. -/
noncomputable def meetLevel (x y : Node Label arity) : Nat :=
  Nat.findGreatest
    (CommonLevel x y)
    (min x.level y.level)

theorem meetLevel_common (x y : Node Label arity) :
    CommonLevel x y (meetLevel x y) := by
  classical
  apply Nat.findGreatest_spec (m := 0)
  · exact Nat.zero_le _
  · exact commonLevel_zero x y

/-- Greatest common prefix, chosen at meetLevel. -/
noncomputable def meetNode (x y : Node Label arity) :
    Node Label arity :=
  Classical.choose (meetLevel_common x y)

theorem meetNode_spec (x y : Node Label arity) :
    meetNode x y ≤ x ∧
      meetNode x y ≤ y ∧
      (meetNode x y).level = meetLevel x y :=
  Classical.choose_spec (meetLevel_common x y)

theorem meetNode_le_left (x y : Node Label arity) :
    meetNode x y ≤ x :=
  (meetNode_spec x y).1

theorem meetNode_le_right (x y : Node Label arity) :
    meetNode x y ≤ y :=
  (meetNode_spec x y).2.1

theorem level_meetNode (x y : Node Label arity) :
    (meetNode x y).level = meetLevel x y :=
  (meetNode_spec x y).2.2

theorem le_meetNode
    {c x y : Node Label arity}
    (hcx : c ≤ x)
    (hcy : c ≤ y) :
    c ≤ meetNode x y := by
  classical
  have hbound :
      c.level ≤ min x.level y.level := by
    exact Nat.le_min
      (node_level_le hcx)
      (node_level_le hcy)
  have hcCommon :
      CommonLevel x y c.level :=
    ⟨c, hcx, hcy, rfl⟩
  have hcle :
      c.level ≤ meetLevel x y :=
    Nat.le_findGreatest hbound hcCommon
  rcases node_lower_linear
      hcx (meetNode_le_left x y) with hcm | hmc
  · exact hcm
  · have hmcle :
        (meetNode x y).level ≤ c.level :=
      node_level_le hmc
    have hlev :
        (meetNode x y).level = c.level := by
      rw [level_meetNode]
      exact Nat.le_antisymm hmcle hcle
    have heq :
        meetNode x y = c :=
      node_eq_of_le_level_eq hmc hlev
    simpa [heq]

theorem node_level_lt_of_lt
    {x y : Node Label arity}
    (hxy : x < y) :
    x.level < y.level := by
  have hle : x.level ≤ y.level :=
    node_level_le hxy.le
  by_contra hnot
  have hrev : y.level ≤ x.level := by omega
  have hlev : x.level = y.level :=
    Nat.le_antisymm hle hrev
  have heq : x = y :=
    node_eq_of_le_level_eq hxy.le hlev
  exact hxy.ne heq

theorem node_covBy_level
    {x y : Node Label arity}
    (hxy : x ⋖ y) :
    y.level = x.level + 1 := by
  have hlt : x.level < y.level :=
    node_level_lt_of_lt hxy.lt
  by_contra hne
  have hgap : x.level + 1 < y.level := by
    omega
  obtain ⟨z, hzy, hzlev⟩ :=
    node_ancestor_exists y (x.level + 1) (by omega)
  have hxz_le : x ≤ z := by
    rcases node_lower_linear hxy.le hzy with hxz | hzx
    · exact hxz
    · have hlevels := node_level_le hzx
      rw [hzlev] at hlevels
      omega
  have hxz : x < z := by
    refine lt_of_le_of_ne hxz_le ?_
    intro heq
    subst z
    rw [hzlev] at *
    omega
  have hzy' : z < y := by
    refine lt_of_le_of_ne hzy ?_
    intro heq
    subst z
    rw [hzlev] at hgap
    omega
  exact (not_covBy_of_lt_of_lt hxz hzy') hxy

noncomputable instance instLevelTreeNode
    [Fintype Label] :
    LevelTree (Node Label arity) where
  level := Node.level
  level_lt := node_level_lt_of_lt
  covBy_level := node_covBy_level
  lower_linear := node_lower_linear
  ancestor_exists := node_ancestor_exists
  level_finite := node_level_finite
  meet := meetNode
  meet_le_left := by
    intro a b hcommon
    exact meetNode_le_left a b
  meet_le_right := by
    intro a b hcommon
    exact meetNode_le_right a b
  le_meet := by
    intro a b c hca hcb
    exact le_meetNode hca hcb

end FreeAncestral
end SuccessorTree
