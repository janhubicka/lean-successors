import SuccessorTree.FreeAncestralMonoid
import Mathlib.Tactic

/-! # Preparatory lemma for M2 on the free ancestral tree

If a shape map sends source level n to target level h+1 and skips h, then
lowering every level-n image to its level-h predecessor is injective.  This is
the meet argument used in the paper proof of M2.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

/-- The predecessor on the skipped level below a source level-n image. -/
noncomputable def lowerImage
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    Node Label arity :=
  LevelTree.ancestor (F x.1) h (by
    change h ≤ (F x.1).level
    have hx := hlevel x.1 x.2
    omega)

@[simp] theorem lowerImage_level
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    (lowerImage F n h hlevel x).level = h := by
  change LevelTree.lev (lowerImage F n h hlevel x) = h
  exact LevelTree.level_ancestor _ _ _

theorem lowerImage_le
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    lowerImage F n h hlevel x ≤ F x.1 :=
  LevelTree.ancestor_le _ _ _

theorem lowerImage_covBy
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    lowerImage F n h hlevel x ⋖ F x.1 := by
  apply LevelTree.covBy_of_le_level_succ
    (lowerImage_le F n h hlevel x)
  have hlo :
      LevelTree.lev (lowerImage F n h hlevel x) = h := by
    exact LevelTree.level_ancestor _ _ _
  have hhi :
      LevelTree.lev (F x.1) = h + 1 := by
    change (F x.1).level = h + 1
    exact hlevel x.1 x.2
  rw [hlo, hhi]

/-- Lowered level-n images are distinct whenever the missing predecessor level
is genuinely skipped by F. -/
theorem lowerImage_injective
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    Function.Injective (lowerImage F n h hlevel) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  have hFne : F x.1 ≠ F y.1 := by
    intro h
    exact hne (F.injective h)
  let z := lowerImage F n h hlevel x
  have hzx : z ≤ F x.1 := by
    exact lowerImage_le F n h hlevel x
  have hzy : z ≤ F y.1 := by
    dsimp [z]
    rw [hxy]
    exact lowerImage_le F n h hlevel y
  have hzxCov : z ⋖ F x.1 := by
    exact lowerImage_covBy F n h hlevel x
  have hzyCov : z ⋖ F y.1 := by
    have hzEq :
        z = lowerImage F n h hlevel y := by
      dsimp [z]
      exact hxy
    rw [hzEq]
    exact lowerImage_covBy F n h hlevel y
  have hmeetLe :
      LevelTree.meet (F x.1) (F y.1) ≤ z :=
    LevelTree.meet_le_of_distinct_covBy
      hzxCov hzyCov hFne le_rfl le_rfl
  have hzMeet :
      z ≤ LevelTree.meet (F x.1) (F y.1) :=
    LevelTree.le_meet hzx hzy
  have hmeetEq :
      LevelTree.meet (F x.1) (F y.1) = z :=
    le_antisymm hmeetLe hzMeet
  have hcommon :
      ∃ r : Node Label arity, r ≤ x.1 ∧ r ≤ y.1 :=
    ⟨rootNode, root_le x.1, root_le y.1⟩
  have hmapMeet :
      F (LevelTree.meet x.1 y.1) =
        LevelTree.meet (F x.1) (F y.1) :=
    F.map_meet hcommon
  apply hskip
  refine ⟨LevelTree.meet x.1 y.1, ?_⟩
  calc
    (F (LevelTree.meet x.1 y.1)).level =
        (LevelTree.meet (F x.1) (F y.1)).level := by
          exact congrArg Node.level hmapMeet
    _ = z.level := by
          exact congrArg Node.level hmeetEq
    _ = h := by
          dsimp [z]
          exact lowerImage_level F n h hlevel x

end FreeAncestral
end SuccessorTree
