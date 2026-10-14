import SuccessorTree.V10.M2BoundaryUpperSelection
import SuccessorTree.V10.ShapeMapFullRecovery
import Mathlib.Tactic

/-!
# Retained ordinary L records and the lower B3 source socle

For any genuine Kpt ShapeMap, the complete old ordinary L atoms are
read back from its image on the strict level-map coordinates. The
generic theorem below is not restricted to a neutral cap or to an
M2 deletion map. It includes both positive and missing directed
binary atoms. This is the low/low comparison needed to reconstruct
the one admissible source socle from a finite L-only B3 witness.
-/

namespace SuccessorTree.V10

/-- Recover every ordinary--ordinary binary atom at the ACTUAL image
numerical addresses of a genuine shape map, not just at a chosen
representative of one type. -/
theorem shapeMap_retained_ordinary_binary
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family)
    (i j : Fin (LevelTree.lev u)) (t : Fin db) :
    (F u).1.2.ageModel.binary
      (kptShapeLevelMap family F i.val)
      (kptShapeLevelMap family F j.val) t =
      u.1.2.lReduct.binary (some i) (some j) t := by
  let ri := retainedSocleIndex family F u i
  let rj := retainedSocleIndex family F u j
  have hri : ri.val = kptShapeLevelMap family F i.val := rfl
  have hrj : rj.val = kptShapeLevelMap family F j.val := rfl
  have hi : kptShapeLevelMap family F i.val < LevelTree.lev (F u) := by
    rw [←hri]
    exact ri.isLt
  have hj : kptShapeLevelMap family F j.val < LevelTree.lev (F u) := by
    rw [←hrj]
    exact rj.isLt
  have hRec := congrArg
    (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
      Q.lReduct.binary (some i) (some j) t)
      (shapeMap_recovers_complete_record family F u)
  change (F u).1.2.lReduct.binary (some ri) (some rj) t =
    u.1.2.lReduct.binary (some i) (some j) t at hRec
  calc
    (F u).1.2.ageModel.binary
      (kptShapeLevelMap family F i.val)
      (kptShapeLevelMap family F j.val) t =
        (F u).1.2.lReduct.binary (some ri) (some rj) t := by
      have hii : typeAgeIndex (LevelTree.lev (F u))
          (kptShapeLevelMap family F i.val) = some ri := by
        simp only [typeAgeIndex, dite_eq_left hi]
        congr 1
      have hjj : typeAgeIndex (LevelTree.lev (F u))
          (kptShapeLevelMap family F j.val) = some rj := by
        simp only [typeAgeIndex, dite_eq_left hj]
        congr 1
      change (F u).1.2.lReduct.binary
        (typeAgeIndex (LevelTree.lev (F u))
          (kptShapeLevelMap family F i.val))
        (typeAgeIndex (LevelTree.lev (F u))
          (kptShapeLevelMap family F j.val)) t = _
      rw [hii,hjj]
    _ = u.1.2.lReduct.binary (some i) (some j) t := hRec

/-- An atom of a Kpt record can be transported through its
explicit-level cast without rewriting the dependent Sigma index. -/
theorem kptRecordAtLevel_binary_cast
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (n : Nat) (x : AdmissibleKptNode family)
    (hx : LevelTree.lev x = n)
    (i j : Fin n) (t : Fin db) :
    x.1.2.lReduct.binary
      (some (Fin.cast hx.symm i))
      (some (Fin.cast hx.symm j)) t =
    (kptRecordAtLevel n x hx).lReduct.binary (some i) (some j) t := by
  rcases x with ⟨⟨k,Q⟩,hAd⟩
  change k = n at hx
  subst k
  rfl

/-- The genuine original source boundary record typed at its uniform
source cut n. This is NOT the deleted target type at level m. -/
noncomputable def m2Boundary_originalType
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a₀ : AdmissibleKptNode family)
    (x : M2BoundaryIndex family a₀) :
    PartialTypeWithE (LevelTree.lev a₀) db du dd :=
  kptRecordAtLevel (LevelTree.lev a₀) x.1 x.2

theorem m2Boundary_original_raw
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a₀ : AdmissibleKptNode family)
    (x : M2BoundaryIndex family a₀) :
    x.1.1 =
      (⟨LevelTree.lev a₀, m2Boundary_originalType family a₀ x⟩ :
        RawPartialTypeNode db du dd) :=
  kptRecordAtLevel_raw (LevelTree.lev a₀) x.1 x.2

/-- Every lower--lower relation of an arbitrary finite B3 L-witness
agrees, on retained numerical levels, with the complete original
source ordinary socle of its anchor boundary node. No E on W. -/
theorem m2Boundary_initial_binary_of_sameSocle
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x0 : M2BoundaryIndex family a₀)
    (W : AgeTestModel db du dd)
    (hSame : SameInitialL W
      (prescribedOrdinarySocle
        (m2Boundary_targetType family F q₀ a₀ hprev hgap x0))
      (LevelTree.lev (F a₀)-1))
    (i j : Fin (LevelTree.lev a₀)) (t : Fin db)
    (hi : kptShapeLevelMap family F i.val < LevelTree.lev (F a₀)-1)
    (hj : kptShapeLevelMap family F j.val < LevelTree.lev (F a₀)-1) :
    W.binary (kptShapeLevelMap family F i.val)
      (kptShapeLevelMap family F j.val) t =
      (m2Boundary_originalType family a₀ x0).lReduct.binary
        (some i) (some j) t := by
  let m := LevelTree.lev (F a₀)-1
  let ti : Nat := kptShapeLevelMap family F i.val
  let tj : Nat := kptShapeLevelMap family F j.val
  have hBin := hSame.2.1 ti tj (by omega) (by omega) t
  have hFType : (F x0.1).1 =
      (⟨m+1,m2Boundary_targetType family F q₀ a₀ hprev hgap x0⟩ :
         RawPartialTypeNode db du dd) :=
    m2Boundary_target_raw family F q₀ a₀ hprev hgap x0
  have hFTarget :
      (prescribedOrdinarySocle
        (m2Boundary_targetType family F q₀ a₀ hprev hgap x0)).binary ti tj t =
        (F x0.1).1.2.ageModel.binary ti tj t := by
    have hiCut : ti ≤ LevelTree.lev (F a₀)-1 := Nat.le_of_lt hi
    have hjCut : tj ≤ LevelTree.lev (F a₀)-1 := Nat.le_of_lt hj
    have hDecode :
        (prescribedOrdinarySocle
          (m2Boundary_targetType family F q₀ a₀ hprev hgap x0)).binary ti tj t =
          (m2Boundary_targetType family F q₀ a₀ hprev hgap x0).ageModel.binary ti tj t := by
      simp [prescribedOrdinarySocle, PartialTypeWithE.ageModel,
        typeAgeIndex, hiCut, hjCut]
    have hAtoms := congrArg
      (fun N : RawPartialTypeNode db du dd =>
        N.2.ageModel.binary ti tj t) hFType
    exact hDecode.trans hAtoms.symm
  have hOldIndexI : i.val < LevelTree.lev x0.1 := by
    rw [x0.2]
    exact i.isLt
  have hOldIndexJ : j.val < LevelTree.lev x0.1 := by
    rw [x0.2]
    exact j.isLt
  let ii : Fin (LevelTree.lev x0.1) := ⟨i.val,hOldIndexI⟩
  let jj : Fin (LevelTree.lev x0.1) := ⟨j.val,hOldIndexJ⟩
  have hOld := shapeMap_retained_ordinary_binary family F x0.1 ii jj t
  have hSource :
      x0.1.1.2.lReduct.binary (some ii) (some jj) t =
        (m2Boundary_originalType family a₀ x0).lReduct.binary
          (some i) (some j) t := by
    have hii : ii = Fin.cast x0.2.symm i := Fin.ext rfl
    have hjj : jj = Fin.cast x0.2.symm j := Fin.ext rfl
    rw [hii, hjj]
    exact kptRecordAtLevel_binary_cast (LevelTree.lev a₀) x0.1 x0.2 i j t
  exact hBin.trans (hFTarget.trans (hOld.trans hSource))

end SuccessorTree.V10
