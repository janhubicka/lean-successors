import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Canonical decomposition of a non-root node

The paper writes a non-root node as
  a = S(parent(a), Dp(a), Dc(a)).
S1--S3 make the parent, parameter list and character unique.
-/

namespace SuccessorTree

namespace STree

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable (S : STree T Label)

/-- The unique predecessor of a non-root node. -/
noncomputable def parent (a : T) (ha : 0 < LevelTree.lev a) : T :=
  LevelTree.ancestor a (LevelTree.lev a - 1) (by omega)

theorem parent_le (a : T) (ha : 0 < LevelTree.lev a) :
    S.parent a ha ≤ a := by
  unfold parent
  exact LevelTree.ancestor_le _ _ _

theorem level_parent (a : T) (ha : 0 < LevelTree.lev a) :
    LevelTree.lev (S.parent a ha) = LevelTree.lev a - 1 := by
  unfold parent
  exact LevelTree.level_ancestor _ _ _

theorem parent_covBy (a : T) (ha : 0 < LevelTree.lev a) :
    S.parent a ha ⋖ a := by
  apply LevelTree.covBy_of_le_level_succ (S.parent_le a ha)
  rw [S.level_parent a ha]
  omega

/-- Successor data of a non-root node. -/
structure Decomposition (a : T) where
  base : T
  params : List T
  char : Label
  succ_eq : S.succ base params char = some a

/-- The canonical decomposition supplied by S3, with the canonical parent as base. -/
noncomputable def decomposition (a : T) (ha : 0 < LevelTree.lev a) :
    S.Decomposition a := by
  obtain ⟨p, c, h⟩ := S.s3 (S.parent_covBy a ha)
  exact ⟨S.parent a ha, p, c, h⟩

@[simp] theorem decomposition_base (a : T) (ha : 0 < LevelTree.lev a) :
    (S.decomposition a ha).base = S.parent a ha := by
  unfold decomposition
  rfl

/-- Paper notation Dp(a). -/
noncomputable def Dp (a : T) (ha : 0 < LevelTree.lev a) : List T :=
  (S.decomposition a ha).params

/-- Paper notation Dc(a). -/
noncomputable def Dc (a : T) (ha : 0 < LevelTree.lev a) : Label :=
  (S.decomposition a ha).char

theorem succ_parent_Dp_Dc (a : T) (ha : 0 < LevelTree.lev a) :
    S.succ (S.parent a ha) (S.Dp a ha) (S.Dc a ha) = some a :=
  (S.decomposition a ha).succ_eq

/-- Any successor presentation of a non-root node uses the canonical parent. -/
theorem base_eq_parent_of_succ
    {a b : T} {p : List T} {c : Label}
    (h : S.succ b p c = some a) :
    b = S.parent a (by
      have hc := S.covBy_of_succ_eq_some h
      rw [LevelTree.covBy_level_eq hc]
      omega) := by
  let ha : 0 < LevelTree.lev a := by
    have hc := S.covBy_of_succ_eq_some h
    rw [LevelTree.covBy_level_eq hc]
    omega
  have hbLevel : LevelTree.lev b = LevelTree.lev a - 1 := by
    have hc := S.covBy_of_succ_eq_some h
    rw [LevelTree.covBy_level_eq hc]
    omega
  exact LevelTree.eq_ancestor_of_le
    (S.covBy_of_succ_eq_some h).le hbLevel (by omega)

/-- S2 makes Dp and Dc independent of the chosen S3 witness. -/
theorem decomposition_unique
    {a b : T} {p : List T} {c : Label}
    (h : S.succ b p c = some a) :
    let ha : 0 < LevelTree.lev a := by
      have hc := S.covBy_of_succ_eq_some h
      rw [LevelTree.covBy_level_eq hc]
      omega
    b = S.parent a ha ∧ p = S.Dp a ha ∧ c = S.Dc a ha := by
  let ha : 0 < LevelTree.lev a := by
    have hc := S.covBy_of_succ_eq_some h
    rw [LevelTree.covBy_level_eq hc]
    omega
  have hcanon := S.succ_parent_Dp_Dc a ha
  exact S.s2 h hcanon

theorem Dp_parameter_level_lt
    (a : T) (ha : 0 < LevelTree.lev a)
    {x : T} (hx : x ∈ S.Dp a ha) :
    LevelTree.lev x < LevelTree.lev (S.parent a ha) := by
  exact S.parameter_level_lt (S.succ_parent_Dp_Dc a ha) hx

/-- The decomposition of the ancestor on level n+1 above a node. -/
noncomputable def DpAt (a : T) (n : Nat)
    (hn : n < LevelTree.lev a) : List T := by
  let b := LevelTree.ancestor a (n + 1) (Nat.succ_le_iff.mpr hn)
  have hb : 0 < LevelTree.lev b := by
    rw [LevelTree.level_ancestor]
    omega
  exact S.Dp b hb

noncomputable def DcAt (a : T) (n : Nat)
    (hn : n < LevelTree.lev a) : Label := by
  let b := LevelTree.ancestor a (n + 1) (Nat.succ_le_iff.mpr hn)
  have hb : 0 < LevelTree.lev b := by
    rw [LevelTree.level_ancestor]
    omega
  exact S.Dc b hb

end STree

end SuccessorTree
