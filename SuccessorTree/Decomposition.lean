import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Canonical decomposition of a non-root node

The paper writes a non-root node as
  a = S(parent(a), Dp(a), Dc(a)).
S1--S3 make the parent, parameter list and character unique.
-/

namespace SuccessorTree

namespace LevelTree

variable {T : Type u} [PartialOrder T] [LevelTree T]

/-- The unique predecessor of a non-root node. -/
noncomputable def parent (a : T) (ha : 0 < lev a) : T :=
  ancestor a (lev a - 1) (by omega)

theorem parent_le (a : T) (ha : 0 < lev a) :
    parent a ha ≤ a := by
  unfold parent
  exact ancestor_le _ _ _

theorem level_parent (a : T) (ha : 0 < lev a) :
    lev (parent a ha) = lev a - 1 := by
  unfold parent
  exact level_ancestor _ _ _

theorem parent_covBy (a : T) (ha : 0 < lev a) :
    parent a ha ⋖ a := by
  apply covBy_of_le_level_succ (parent_le a ha)
  rw [level_parent a ha]
  omega

end LevelTree

namespace STree

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable (S : STree T Label)

/-- Successor data of a non-root node. -/
structure Decomposition (a : T) where
  base : T
  params : List T
  char : Label
  succ_eq : S.succ base params char = some a

/-- The canonical decomposition supplied by S3, with the canonical parent as base. -/
noncomputable def decomposition (a : T) (ha : 0 < LevelTree.lev a) :
    S.Decomposition a :=
  let hcov := LevelTree.parent_covBy a ha
  let p := Classical.choose (S.s3 hcov)
  let hc := Classical.choose_spec (S.s3 hcov)
  let c := Classical.choose hc
  let hs := Classical.choose_spec hc
  ⟨LevelTree.parent a ha, p, c, hs⟩

@[simp] theorem decomposition_base (a : T) (ha : 0 < LevelTree.lev a) :
    (S.decomposition a ha).base = LevelTree.parent a ha := by
  unfold decomposition
  rfl

/-- Paper notation Dp(a). -/
noncomputable def Dp (a : T) (ha : 0 < LevelTree.lev a) : List T :=
  (S.decomposition a ha).params

/-- Paper notation Dc(a). -/
noncomputable def Dc (a : T) (ha : 0 < LevelTree.lev a) : Label :=
  (S.decomposition a ha).char

theorem succ_parent_Dp_Dc (a : T) (ha : 0 < LevelTree.lev a) :
    S.succ (LevelTree.parent a ha) (S.Dp a ha) (S.Dc a ha) = some a :=
  (S.decomposition a ha).succ_eq

/-- S2 makes Dp and Dc independent of any alternative successor presentation. -/
theorem decomposition_unique
    {a b : T} {p : List T} {c : Label}
    (h : S.succ b p c = some a) :
    let ha : 0 < LevelTree.lev a := by
      have hc := S.covBy_of_succ_eq_some h
      rw [LevelTree.covBy_level_eq hc]
      omega
    b = LevelTree.parent a ha ∧
      p = S.Dp a ha ∧
      c = S.Dc a ha := by
  let ha : 0 < LevelTree.lev a := by
    have hc := S.covBy_of_succ_eq_some h
    rw [LevelTree.covBy_level_eq hc]
    omega
  have hcanon := S.succ_parent_Dp_Dc a ha
  exact S.s2 h hcanon

theorem Dp_parameter_level_lt
    (a : T) (ha : 0 < LevelTree.lev a)
    {x : T} (hx : x ∈ S.Dp a ha) :
    LevelTree.lev x < LevelTree.lev (LevelTree.parent a ha) := by
  exact S.parameter_level_lt (S.succ_parent_Dp_Dc a ha) hx

/-- The decomposition parameters of the ancestor of a on level n+1. -/
noncomputable def DpAt (a : T) (n : Nat)
    (hn : n < LevelTree.lev a) : List T :=
  let b := LevelTree.ancestor a (n + 1) (Nat.succ_le_iff.mpr hn)
  let hb : 0 < LevelTree.lev b := by
    rw [LevelTree.level_ancestor]
    omega
  S.Dp b hb

/-- The decomposition character of the ancestor of a on level n+1. -/
noncomputable def DcAt (a : T) (n : Nat)
    (hn : n < LevelTree.lev a) : Label :=
  let b := LevelTree.ancestor a (n + 1) (Nat.succ_le_iff.mpr hn)
  let hb : 0 < LevelTree.lev b := by
    rw [LevelTree.level_ancestor]
    omega
  S.Dc b hb

end STree

end SuccessorTree
