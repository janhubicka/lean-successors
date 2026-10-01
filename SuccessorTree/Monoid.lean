import SuccessorTree.ShapePreserving
import Mathlib.Tactic

/-!
# The M1--M3 family of shape-preserving maps

This file formalizes Definition `def:sntree` from the paper.  In particular,
no nonemptiness of levels is assumed: the theorem `SMTree.level_nonempty`
below derives it from M3 (duplication).  This is important because the paper
uses the total level function \(\widetilde F(n)\) only after introducing
M1--M3.
-/

namespace SuccessorTree

namespace ShapeMap

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The set of levels met by the range of a shape-preserving map. -/
def levelRange (F : ShapeMap S) : Set Nat :=
  {n | ∃ a : T, LevelTree.lev (F a) = n}

/-- Paper terminology: `F` skips level `m`. -/
def Skips (F : ShapeMap S) (m : Nat) : Prop :=
  m ∉ F.levelRange

/-- Paper terminology: `F` skips only level `m`. -/
def SkipsOnly (F : ShapeMap S) (m : Nat) : Prop :=
  F.levelRange = {n | n ≠ m}

end ShapeMap

/-- An \((\mathcal S,\mathcal M)\)-tree: a family of shape-preserving maps
satisfying M1--M3.

M2 is written using a node `a` on level `n` rather than a pre-existing
total level map.  Level preservation makes the value independent of `a`,
and M3 below proves that every such level is inhabited.  Thus this is
equivalent to the paper's formulation while avoiding a hidden nonemptiness
assumption in the definition. -/
structure SMTree {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T] (S : STree T Label) where
  M : Set (ShapeMap S)

  /-- M1: identity. -/
  id_mem : ShapeMap.id S ∈ M

  /-- M1: closure under composition. -/
  comp_mem : ∀ {F G : ShapeMap S}, F ∈ M → G ∈ M → F.comp G ∈ M

  /-- M1: closure under the pointwise fusion limit used in the paper. -/
  fusion_mem :
    ∀ (F : Nat → ShapeMap S)
      (hmem : ∀ i : Nat, F i ∈ M)
      (hstable : ShapeMap.FusionStable F),
      ShapeMap.fusionLimit F hstable ∈ M

  /-- M2: decomposition by a map which skips precisely the last missing
  target level.  Equality is required on the restriction through level `n`. -/
  m2 :
    ∀ (n : Nat) (F : ShapeMap S), F ∈ M →
    ∀ (a : T), LevelTree.lev a = n →
      0 < LevelTree.lev (F a) →
      F.Skips (LevelTree.lev (F a) - 1) →
      ∃ F1 F2 : ShapeMap S,
        F1 ∈ M ∧
        F2 ∈ M ∧
        F2.SkipsOnly (LevelTree.lev (F a) - 1) ∧
        ∀ x : T, LevelTree.lev x ≤ n → F2 (F1 x) = F x

  /-- M3: duplication.  The equation
  `succ b p c = some (D b)` is the Option-valued version of
  \(D(b)=\mathcal S(b,\bar p,c)\). -/
  m3 :
    ∀ (n m : Nat), n < m →
      ∃ D : ShapeMap S,
        D ∈ M ∧
        D.SkipsOnly m ∧
        ∀ (a b : T) (p : List T) (c : Label) (s : T),
          LevelTree.lev a = n →
          LevelTree.lev b = m →
          S.succ a p c = some s →
          s ≤ b →
          S.succ b p c = some (D b)

namespace SMTree

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- M3 by itself forces every level of the underlying tree to be inhabited.
Hence the total level-function notation used after Definition `def:sntree`
does not require an additional hypothesis. -/
theorem level_nonempty (H : SMTree S) (k : Nat) :
    ∃ a : T, LevelTree.lev a = k := by
  obtain ⟨D, hDM, hskip, hdup⟩ := H.m3 0 (k + 1) (by omega)
  have hk : k ∈ D.levelRange := by
    rw [hskip]
    simp
  rcases hk with ⟨a, ha⟩
  exact ⟨D a, ha⟩

/-- The paper's total level function \(\widetilde F\), now justified by
`level_nonempty`. -/
noncomputable def levelMap (H : SMTree S) (F : ShapeMap S) (n : Nat) : Nat :=
  let a := Classical.choose (H.level_nonempty n)
  LevelTree.lev (F a)

theorem levelMap_eq (H : SMTree S) (F : ShapeMap S) {a : T} :
    H.levelMap F (LevelTree.lev a) = LevelTree.lev (F a) := by
  unfold levelMap
  let x := Classical.choose (H.level_nonempty (LevelTree.lev a))
  have hx : LevelTree.lev x = LevelTree.lev a :=
    Classical.choose_spec (H.level_nonempty (LevelTree.lev a))
  exact F.level_eq_of_level_eq hx

/-- Shape-preserving maps induce strictly increasing maps on levels. -/
theorem levelMap_strictMono (H : SMTree S) (F : ShapeMap S) :
    StrictMono (H.levelMap F) := by
  intro n m hnm
  obtain ⟨a, ha⟩ := H.level_nonempty n
  obtain ⟨b, hb⟩ := H.level_nonempty m
  have hab : LevelTree.lev a < LevelTree.lev b := by omega
  have hFab := F.level_lt_of_level_lt hab
  calc
    H.levelMap F n = LevelTree.lev (F a) := by
      simpa [ha] using (H.levelMap_eq F (a := a))
    _ < LevelTree.lev (F b) := hFab
    _ = H.levelMap F m := by
      simpa [hb] using (H.levelMap_eq F (a := b)).symm

/-- The range of the total level map is exactly the set of levels met by the
range of `F`. -/
theorem range_levelMap (H : SMTree S) (F : ShapeMap S) :
    Set.range (H.levelMap F) = F.levelRange := by
  ext k
  constructor
  · rintro ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := H.level_nonempty n
    refine ⟨a, ?_⟩
    have h := H.levelMap_eq F (a := a)
    rw [ha] at h
    exact h.symm
  · rintro ⟨a, ha⟩
    refine ⟨LevelTree.lev a, ?_⟩
    exact (H.levelMap_eq F (a := a)).trans ha

end SMTree

end SuccessorTree
