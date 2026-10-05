import SuccessorTree.FatTree.A4HistoryRows

/-!
# Geometric realization of history rows

The manuscript block `h = w_j P` obtained from a history is not merely an
admissible row: its whole one-step lift is contained in the corresponding
ambient fat-tree lift.  This is the geometric bridge needed to turn replay
Hales--Jewett histories into actual fat-tree lines.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree
namespace TraceHistoryState

variable (H : SMTree S)

/-- The canonical extension of a history head sends every immediate successor
of the original source level into the ambient lift through the next history
cut. -/
theorem headRow_oneLift_subset
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    H.canonicalExtension
          ((headRow H U a i P).representative H) (U.cut a) ''
        ImmediateSuccessors (T := T)
          (TreeLevel (T := T) (U.cut a))
      ⊆
    U.liftTo H a (a + i + 1) (by omega)
      (TreeLevel (T := T) (U.cut a)) := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with ⟨x, hxLevel, hxy⟩
  let d := U.cut a
  let m := U.cut (a + i)
  let h := headRow H U a i P
  let C : MMap H :=
    H.canonicalExtension (h.representative H) d
  let R : MMap H := U.rowExtension H (a + i)

  obtain ⟨params, ch, hsxy⟩ := S.s3 hxy
  obtain ⟨t, hPt, htPy⟩ := P.toMMap.map.weak_succ' hsxy

  have hx : LevelTree.lev x = d := hxLevel
  have hPx :
      LevelTree.lev (P.toMMap x) = m := by
    dsimp [d, m]
    exact P.level_apply H U a i hxLevel

  have htCover : P.toMMap x ⋖ t :=
    S.covBy_of_succ_eq_some hPt
  have htLevel : LevelTree.lev t = m + 1 := by
    rw [LevelTree.covBy_level_eq htCover, hPx]

  have hRlevels :
      H.levelMap R.map (LevelTree.lev t) =
        H.levelMap R.map (LevelTree.lev (P.toMMap x)) + 1 := by
    rw [htLevel, hPx]
    dsimp [R, m]
    calc
      H.levelMap (U.rowExtension H (a + i)).map
          (U.cut (a + i) + 1) =
          U.cut (a + i + 1) :=
        U.rowExtension_level_succ H (a + i)
      _ = (U.row (a + i)).rowEndLevel H + 1 :=
        (U.row_cut (a + i)).symm
      _ =
          H.levelMap (U.rowExtension H (a + i)).map
            (U.cut (a + i)) + 1 := by
        rw [U.rowExtension_level_at_cut H (a + i)]

  have hRt :
      S.succ (R (P.toMMap x))
          ((params.map P.toMMap.map).map R.map) ch =
        some (R t) := by
    exact H.succ_eq_of_consecutive_levels R.map hPt hRlevels

  have hClevels :
      H.levelMap C.map (LevelTree.lev y) =
        H.levelMap C.map (LevelTree.lev x) + 1 := by
    have hyLevel : LevelTree.lev y = d + 1 :=
      LevelTree.covBy_level_eq hxy
    rw [hyLevel, hx]
    dsimp [C, d]
    calc
      H.levelMap
          (H.canonicalExtension (h.representative H) (U.cut a)).map
          (U.cut a + 1) =
          H.levelMap (h.representative H).map (U.cut a) + 1 :=
        H.canonicalExtension_level_succ
          (h.representative H) (U.cut a) (U.cut a) le_rfl
      _ =
          H.levelMap
            (H.canonicalExtension (h.representative H) (U.cut a)).map
            (U.cut a) + 1 := by
        rw [H.canonicalExtension_level_at_prefix
          (h.representative H) (U.cut a)]

  have hCy :
      S.succ (C x) (params.map C.map) ch =
        some (C y) := by
    exact H.succ_eq_of_consecutive_levels C.map hsxy hClevels

  have hCx :
      C x = R (P.toMMap x) := by
    dsimp [C, R, h, d]
    rw [H.canonicalExtension_agrees
      ((headRow H U a i P).representative H)
      (U.cut a) x (by simpa [hxLevel])]
    exact headRow_representative_agrees H U a i P x
      (by simpa [hxLevel])

  have hparamPoint :
      ∀ q ∈ params, C q = R (P.toMMap q) := by
    intro q hq
    have hqLt : LevelTree.lev q < d := by
      have hq0 := S.parameter_level_lt hsxy hq
      simpa [hx] using hq0
    have hqLe : LevelTree.lev q ≤ d := Nat.le_of_lt hqLt
    have hCq :
        C q = (headRow H U a i P).representative H q := by
      dsimp [C, d]
      exact H.canonicalExtension_agrees
        ((headRow H U a i P).representative H) (U.cut a) q hqLe
    have hhq :
        (headRow H U a i P).representative H q =
          R (P.toMMap q) := by
      dsimp [R]
      exact headRow_representative_agrees H U a i P q hqLe
    exact hCq.trans hhq

  have hparamEq :
      params.map C.map =
        (params.map P.toMMap.map).map R.map := by
    induction params with
    | nil => rfl
    | cons q qs ih =>
        have hqEq : C q = R (P.toMMap q) :=
          hparamPoint q (by simp)
        have htail :
            qs.map C.map =
              (qs.map P.toMMap.map).map R.map := by
          apply ih
          intro r hr
          exact hparamPoint r (by simp [hr])
        simp only [List.map_cons]
        rw [hqEq, htail]

  have hRt' :
      S.succ (C x) (params.map C.map) ch =
        some (R t) := by
    rw [hCx, hparamEq]
    exact hRt

  have hCyRt : C y = R t := by
    exact Option.some.inj (hCy.symm.trans hRt')

  have hprev :
      P.toMMap x ∈
        U.liftTo H a (a + i) (by omega)
          (TreeLevel (T := T) (U.cut a)) :=
    P.image_mem_lift x hxLevel
  have htSucc :
      t ∈ ImmediateSuccessors (T := T)
        (U.liftTo H a (a + i) (by omega)
          (TreeLevel (T := T) (U.cut a))) :=
    ⟨P.toMMap x, hprev, htCover⟩
  have hlast :
      R t ∈ U.oneLift H (a + i)
        (U.liftTo H a (a + i) (by omega)
          (TreeLevel (T := T) (U.cut a))) :=
    ⟨t, htSucc, rfl⟩

  have hsplit :=
    U.liftTo_split H a (a + i) (a + i + 1)
      (by omega) (by omega)
      (TreeLevel (T := T) (U.cut a))
  have hone :=
    U.liftTo_succ H (a + i)
      (U.liftTo H a (a + i) (by omega)
        (TreeLevel (T := T) (U.cut a)))
  have htarget :
      R t ∈
        U.liftTo H a (a + i + 1) (by omega)
          (TreeLevel (T := T) (U.cut a)) := by
    rw [hsplit, hone]
    exact hlast
  rw [hCyRt]
  exact htarget

end TraceHistoryState
end FatTree
end SMTree
end SuccessorTree
