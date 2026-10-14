import SuccessorTree.V10.M2B3SocleAge
import SuccessorTree.V10.LevelRemovalTopDeletePrefix
import SuccessorTree.V10.M2B2Transfer
import SuccessorTree.V10.M2BoundaryFamily
import Mathlib.Tactic

/-!
# Intrinsic finite-cut boundary records for the M2 partial prescription

Every original Kpt node at the first source level n after the gap
produces a genuine deleted boundary record D(x) at level m and a
genuine output record F(x) at level m+1. We type these records at
their *fixed* common levels rather than treating the dependent
Sigma indices as definitionally identical.

The old full L+ predecessor equality makes the output an extension
of the deleted input (B1). Injectivity of the genuine deletion
ShapeMap ensures that these input records are indexed uniquely.
The remaining B2 compatible-socle transport is treated separately.
No extension map, M2 axiom, or artificial boundary age is assumed.
-/

namespace SuccessorTree.V10

/-- A complete Kpt record with its dependent index cast to a
certified explicit level. -/
def kptRecordAtLevel
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (n : Nat) (x : AdmissibleKptNode family)
    (h : LevelTree.lev x = n) : PartialTypeWithE n db du dd :=
  h ▸ x.1.2

/-- The level cast preserves the entire dependent Sigma node, not
only the L reduct. -/
theorem kptRecordAtLevel_raw
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (n : Nat) (x : AdmissibleKptNode family)
    (h : LevelTree.lev x = n) :
    x.1 = (⟨n,kptRecordAtLevel n x h⟩ :
      RawPartialTypeNode db du dd) := by
  rcases x with ⟨⟨k,T⟩,hAd⟩
  change k = n at h
  subst k
  rfl

/-- All original source nodes on the first level after the image
gap, in all components of the admissible Kpt forest. -/
def M2BoundaryIndex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a₀ : AdmissibleKptNode family) : Type :=
  {x : AdmissibleKptNode family // LevelTree.lev x = LevelTree.lev a₀}

/-- The complete F-image boundary type has exactly one more ordinary
coordinate than the intrinsic deleted boundary image. -/
theorem m2Boundary_target_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    LevelTree.lev (F x.1) = (LevelTree.lev (F a₀) - 1) + 1 := by
  have hLevel := F.level_eq_of_level_eq x.2
  omega

/-- At every boundary source node, the genuine global deletion
map lands at the one fixed target level m. -/
theorem m2Boundary_deleted_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    LevelTree.lev
      (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x.1) =
      LevelTree.lev (F a₀) - 1 := by
  have hNotLow : ¬ LevelTree.lev x.1 < LevelTree.lev a₀ := by
    have hxLevel : LevelTree.lev x.1 = LevelTree.lev a₀ := x.2
    omega
  have hExpr :=
    uniformGapDeletedShapeMap_level family F q₀ a₀ hprev hgap x.1
  rw [if_neg hNotLow] at hExpr
  rw [hExpr, F.level_eq_of_level_eq x.2]

/-- The actual complete deleted input record of a source boundary
node, transported to its common numerical level m. -/
noncomputable def m2Boundary_sourceType
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    PartialTypeWithE (LevelTree.lev (F a₀)-1) db du dd :=
  kptRecordAtLevel
    (LevelTree.lev (F a₀)-1)
    (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x.1)
    (m2Boundary_deleted_level family F q₀ a₀ hprev hgap x)

/-- The actual complete F-image output at the restored boundary
level m+1. -/
noncomputable def m2Boundary_targetType
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    PartialTypeWithE ((LevelTree.lev (F a₀)-1)+1) db du dd :=
  kptRecordAtLevel
    ((LevelTree.lev (F a₀)-1)+1) (F x.1)
    (m2Boundary_target_level family F q₀ a₀ hprev hgap x)

/-- Source input and genuine D-image are literally the same complete
L+ node, including E and absent relation bits. -/
theorem m2Boundary_source_raw
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x.1).1 =
      (⟨LevelTree.lev (F a₀)-1,
        m2Boundary_sourceType family F q₀ a₀ hprev hgap x⟩ :
        RawPartialTypeNode db du dd) :=
  kptRecordAtLevel_raw
    (LevelTree.lev (F a₀)-1)
    (uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap x.1)
    (m2Boundary_deleted_level family F q₀ a₀ hprev hgap x)

/-- Output and genuine F-image are also literally the same complete
L+ record. -/
theorem m2Boundary_target_raw
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    (F x.1).1 =
      (⟨(LevelTree.lev (F a₀)-1)+1,
        m2Boundary_targetType family F q₀ a₀ hprev hgap x⟩ :
        RawPartialTypeNode db du dd) :=
  kptRecordAtLevel_raw
    ((LevelTree.lev (F a₀)-1)+1) (F x.1)
    (m2Boundary_target_level family F q₀ a₀ hprev hgap x)

/-- Boundary source records are INJECTIVELY indexed by original
source nodes because D is a genuine injective Kpt ShapeMap.
This makes the restoration prescription single-valued. -/
theorem m2Boundary_source_injective
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    Function.Injective
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap) := by
  intro x y hSame
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  have hRaw : (D x.1).1 = (D y.1).1 := by
    calc
      (D x.1).1 =
          (⟨LevelTree.lev (F a₀)-1,
            m2Boundary_sourceType family F q₀ a₀ hprev hgap x⟩ :
            RawPartialTypeNode db du dd) :=
        m2Boundary_source_raw family F q₀ a₀ hprev hgap x
      _ = (⟨LevelTree.lev (F a₀)-1,
            m2Boundary_sourceType family F q₀ a₀ hprev hgap y⟩ :
            RawPartialTypeNode db du dd) :=
        congrArg (Sigma.mk (LevelTree.lev (F a₀)-1)) hSame
      _ = (D y.1).1 :=
        (m2Boundary_source_raw family F q₀ a₀ hprev hgap y).symm
  apply Subtype.ext
  apply D.injective'
  exact Subtype.ext hRaw

/-- Actual M2 boundary B1: the complete target record extends its
deleted input by precisely its final ordinary L+ coordinate. -/
theorem m2Boundary_B1
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    (m2Boundary_targetType family F q₀ a₀ hprev hgap x).restrict
      (Nat.le_succ (LevelTree.lev (F a₀)-1)) =
    m2Boundary_sourceType family F q₀ a₀ hprev hgap x := by
  let m := LevelTree.lev (F a₀)-1
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  have hRaw : (D x.1).1 =
      rawPartialTypeAncestor (F x.1).1 m (by
        have hLevel : (F x.1).1.1 = (F a₀).1.1 :=
          F.level_eq_of_level_eq x.2
        dsimp [m]
        omega) :=
    uniformGapDeletedShapeMap_boundary_raw_ancestor
      family F q₀ a₀ hprev hgap x.1 x.2
  have hEq :
      (⟨m,m2Boundary_sourceType family F q₀ a₀ hprev hgap x⟩ :
         RawPartialTypeNode db du dd) =
      (⟨m,(m2Boundary_targetType family F q₀ a₀ hprev hgap x).restrict
            (Nat.le_succ m)⟩ :
         RawPartialTypeNode db du dd) := by
    calc
      (⟨m,m2Boundary_sourceType family F q₀ a₀ hprev hgap x⟩ :
         RawPartialTypeNode db du dd) =
         (D x.1).1 :=
        (m2Boundary_source_raw family F q₀ a₀ hprev hgap x).symm
      _ = rawPartialTypeAncestor (F x.1).1 m (by
           have hLevel : (F x.1).1.1 = (F a₀).1.1 :=
             F.level_eq_of_level_eq x.2
           dsimp [m]
           omega) := hRaw
      _ = rawPartialTypeAncestor
           (⟨m+1,m2Boundary_targetType family F q₀ a₀ hprev hgap x⟩ :
              RawPartialTypeNode db du dd) m (Nat.le_succ m) := by
        rw [m2Boundary_target_raw family F q₀ a₀ hprev hgap x]
      _ = (⟨m,(m2Boundary_targetType family F q₀ a₀ hprev hgap x).restrict
              (Nat.le_succ m)⟩ : RawPartialTypeNode db du dd) := rfl
  exact (eq_of_heq (Sigma.mk.inj_iff.mp hEq).2).symm

end SuccessorTree.V10
