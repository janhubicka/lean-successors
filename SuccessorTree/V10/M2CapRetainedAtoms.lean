import SuccessorTree.V10.ShapeMapFullRecovery
import SuccessorTree.V10.NonedgePaddingSocleCap
import SuccessorTree.V10.M2SourceTypeAge
import Mathlib.Tactic

/-!
# Every ordinary L record in a common capped image

The full retained record of one genuine ShapeMap gives the complete
induced L record on the image of the source's old ordinary socle. A
neutral cap copies all these source atoms literally, so every directed
positive or negative pair, singleton and diagonal atom is recovered.
No M2, B3 or age-preservation assumption on the ShapeMap is used.
-/
namespace SuccessorTree.V10

/-- Every ordinary L pair of a padded source is recovered inside the
single capped image at its actual level-map coordinates. -/
theorem shapeMap_socleCap_all_binary
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (i j : Nat) (hi : i < B.size) (hj : j < B.size)
    (t : Fin db) :
    let u := NonedgePadding.socleCapNode family B hAvoidB
    ∃ (_hiF : kptShapeLevelMap family F i < LevelTree.lev (F u))
      (_hjF : kptShapeLevelMap family F j < LevelTree.lev (F u)),
      (F u).1.2.ageModel.binary (kptShapeLevelMap family F i)
        (kptShapeLevelMap family F j) t = B.L.binary i j t := by
  let u := NonedgePadding.socleCapNode family B hAvoidB
  let lambda := kptShapeLevelMap family F
  have hu : LevelTree.lev u = B.size := rfl
  let fi : Fin (LevelTree.lev u) := ⟨i,by simpa only [hu] using hi⟩
  let fj : Fin (LevelTree.lev u) := ⟨j,by simpa only [hu] using hj⟩
  let ri := retainedSocleIndex family F u fi
  let rj := retainedSocleIndex family F u fj
  have hri : ri.val = lambda i := rfl
  have hrj : rj.val = lambda j := rfl
  have hiF : lambda i < LevelTree.lev (F u) := by
    rw [←hri]
    exact ri.isLt
  have hjF : lambda j < LevelTree.lev (F u) := by
    rw [←hrj]
    exact rj.isLt
  have hRec := congrArg
    (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
      Q.lReduct.binary (some fi) (some fj) t)
      (shapeMap_recovers_complete_record family F u)
  change (F u).1.2.lReduct.binary (some ri) (some rj) t =
    u.1.2.lReduct.binary (some fi) (some fj) t at hRec
  refine ⟨hiF,hjF,?_⟩
  calc
    (F u).1.2.ageModel.binary (lambda i) (lambda j) t =
      (F u).1.2.lReduct.binary (some ri) (some rj) t := by
        have hIndexI : typeAgeIndex (LevelTree.lev (F u)) (lambda i) = some ri := by
          simp only [typeAgeIndex, dite_eq_left hiF]
          congr 1
        have hIndexJ : typeAgeIndex (LevelTree.lev (F u)) (lambda j) = some rj := by
          simp only [typeAgeIndex, dite_eq_left hjF]
          congr 1
        change (F u).1.2.lReduct.binary
          (typeAgeIndex (LevelTree.lev (F u)) (lambda i))
          (typeAgeIndex (LevelTree.lev (F u)) (lambda j)) t = _
        rw [hIndexI,hIndexJ]
    _ = u.1.2.lReduct.binary (some fi) (some fj) t := hRec
    _ = B.L.binary i j t := by
      change (NonedgePadding.socleCap B).L.binary i j t = B.L.binary i j t
      exact NonedgePadding.twoNeutralL_old_binary B i j hi hj t

/-- Full singleton and diagonal L record on any old ordinary coordinate
survives the cap and the arbitrary shape-preserving image. -/
theorem shapeMap_socleCap_all_singletons
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (i : Nat) (hi : i < B.size) :
    let u := NonedgePadding.socleCapNode family B hAvoidB
    ∃ (_hiF : kptShapeLevelMap family F i < LevelTree.lev (F u)),
      (∀ t : Fin du,
        (F u).1.2.ageModel.unary (kptShapeLevelMap family F i) t =
          B.L.unary i t) ∧
      (∀ t : Fin dd,
        (F u).1.2.ageModel.diagonal (kptShapeLevelMap family F i) t =
          B.L.diagonal i t) := by
  let u := NonedgePadding.socleCapNode family B hAvoidB
  let lambda := kptShapeLevelMap family F
  have hu : LevelTree.lev u = B.size := rfl
  let fi : Fin (LevelTree.lev u) := ⟨i,by simpa only [hu] using hi⟩
  let ri := retainedSocleIndex family F u fi
  have hri : ri.val = lambda i := rfl
  have hiF : lambda i < LevelTree.lev (F u) := by
    rw [←hri]
    exact ri.isLt
  have hIndexI : typeAgeIndex (LevelTree.lev (F u)) (lambda i) = some ri := by
    simp only [typeAgeIndex,dite_eq_left hiF]
    congr 1
  have hRec := shapeMap_recovers_complete_record family F u
  refine ⟨hiF, ?_, ?_⟩
  · intro t
    have hAtom := congrArg
      (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
        Q.lReduct.unary (some fi) t) hRec
    change (F u).1.2.lReduct.unary (some ri) t =
      u.1.2.lReduct.unary (some fi) t at hAtom
    calc
      (F u).1.2.ageModel.unary (lambda i) t =
        (F u).1.2.lReduct.unary (some ri) t := by
          change (F u).1.2.lReduct.unary
            (typeAgeIndex (LevelTree.lev (F u)) (lambda i)) t = _
          rw [hIndexI]
      _ = u.1.2.lReduct.unary (some fi) t := hAtom
      _ = B.L.unary i t := by
        change (NonedgePadding.socleCap B).L.unary i t = _
        exact NonedgePadding.twoNeutralL_old_unary B i hi t
  · intro t
    have hAtom := congrArg
      (fun Q : PartialTypeWithE (LevelTree.lev u) db du dd =>
        Q.lReduct.diagonal (some fi) t) hRec
    change (F u).1.2.lReduct.diagonal (some ri) t =
      u.1.2.lReduct.diagonal (some fi) t at hAtom
    calc
      (F u).1.2.ageModel.diagonal (lambda i) t =
        (F u).1.2.lReduct.diagonal (some ri) t := by
          change (F u).1.2.lReduct.diagonal
            (typeAgeIndex (LevelTree.lev (F u)) (lambda i)) t = _
          rw [hIndexI]
      _ = u.1.2.lReduct.diagonal (some fi) t := hAtom
      _ = B.L.diagonal i t := by
        change (NonedgePadding.socleCap B).L.diagonal i t = _
        exact NonedgePadding.twoNeutralL_old_diagonal B i hi t

end SuccessorTree.V10
