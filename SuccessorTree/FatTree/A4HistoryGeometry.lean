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


/-- Appending the history head to the ambient prefix at `a` occurs exactly at
depth `a+i+1` in the original fat tree. -/
theorem headRow_stemAt
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    StemAt H
      (FiniteFatTree.appendRow H (U.initialSegment H a)
        (headRow H U a i P))
      U (a + i + 1) := by
  let x : FiniteFatTree H := U.initialSegment H a
  let h : AM H x.terminalCut 1 := by
    change AM H (U.cut a) 1
    exact headRow H U a i P
  let V : FiniteFatTree H := FiniteFatTree.appendRow H x h
  let Z : FiniteFatTree H := U.initialSegment H (a + i + 1)

  have hxheight : x.height = a := rfl
  have hVheight : V.height = a + 1 := rfl
  have hZheight : Z.height = a + i + 1 := rfl

  let idx : Fin (V.height + 1) → Fin (Z.height + 1) :=
    fun k =>
      if hk : k.1 ≤ a then
        ⟨k.1, by
          change k.1 < a + i + 2
          omega⟩
      else
        ⟨a + i + 1, by
          change a + i + 1 < a + i + 2
          omega⟩

  have hidxStrict : StrictMono idx := by
    intro p q hpq
    by_cases hq : q.1 ≤ a
    · have hp : p.1 ≤ a := by omega
      simp [idx, hp, hq]
      exact hpq
    · have hqeq : q.1 = a + 1 := by
        have hqbound : q.1 < a + 2 := by
          simpa [V, hVheight] using q.2
        omega
      have hp : p.1 ≤ a := by omega
      simp [idx, hp, hq, hqeq]
      omega

  have hcut : ∀ k : Fin (V.height + 1), V.cut k = Z.cut (idx k) := by
    intro k
    by_cases hk : k.1 ≤ a
    · let ka : Fin (x.height + 1) :=
        ⟨k.1, by
          change k.1 < a + 1
          omega⟩
      have hkcast : ka.castSucc = k := by
        apply Fin.ext
        rfl
      calc
        V.cut k = V.cut ka.castSucc := by rw [hkcast]
        _ = x.cut ka :=
          FiniteFatTree.appendRow_cut_old H x h ka
        _ = U.cut k.1 := rfl
        _ = Z.cut (idx k) := by
          simp [idx, hk, Z]
    · have hkeq : k.1 = a + 1 := by
        have hkbound : k.1 < a + 2 := by
          simpa [V, hVheight] using k.2
        omega
      have hkLast : k = Fin.last V.height := by
        apply Fin.ext
        simpa [hVheight] using hkeq
      calc
        V.cut k = V.terminalCut := by rw [hkLast]
        _ = h.rowEndLevel H + 1 :=
          FiniteFatTree.appendRow_terminalCut H x h
        _ = U.cut (a + i + 1) := by
          change
            (headRow H U a i P).rowEndLevel H + 1 =
              U.cut (a + i + 1)
          exact headRow_nextCut H U a i P
        _ = Z.cut (idx k) := by
          simp [idx, hk, Z]

  have hlift :
      ∀ r : Fin V.height,
        V.oneLift H r
            (TreeLevel (T := T) (V.cut r.castSucc)) ⊆
          Z.liftTo H (idx r.castSucc) (idx r.succ)
            (le_of_lt (hidxStrict (by
              change r.1 < r.1 + 1
              omega)))
            (TreeLevel (T := T) (Z.cut (idx r.castSucc))) := by
    intro r
    by_cases hr : r.1 < a
    · let ra : Fin a := ⟨r.1, hr⟩
      have hrV : (⟨r.1, by omega⟩ : Fin V.height) = r := Fin.ext rfl
      have hidx0 : idx r.castSucc =
          (⟨r.1, by
            change r.1 < a + i + 2
            omega⟩ : Fin (Z.height + 1)) := by
        apply Fin.ext
        simp [idx]
        omega
      have hidx1 : idx r.succ =
          (⟨r.1 + 1, by
            change r.1 + 1 < a + i + 2
            omega⟩ : Fin (Z.height + 1)) := by
        apply Fin.ext
        simp [idx]
        omega
      have hVprefix :
          V.initialSegment H a (by
            rw [hVheight]
            omega) = x := by
        dsimp [V]
        exact FiniteFatTree.appendRow_initialSegment H x h
      have hVone :
          (V.initialSegment H a (by
            rw [hVheight]
            omega)).oneLift H ra
              (TreeLevel (T := T) (U.cut r.1)) =
            V.oneLift H r
              (TreeLevel (T := T) (U.cut r.1)) := by
        simpa [ra, hrV] using
          V.initialSegment_oneLift H a
            (by rw [hVheight]; omega) ra
            (TreeLevel (T := T) (U.cut r.1))
      have hxone :
          x.oneLift H ra
              (TreeLevel (T := T) (U.cut r.1)) =
            U.oneLift H r.1
              (TreeLevel (T := T) (U.cut r.1)) := by
        simpa [x, ra] using
          U.initialSegment_oneLift H a ra
            (TreeLevel (T := T) (U.cut r.1))
      have hsource :
          V.oneLift H r
              (TreeLevel (T := T) (V.cut r.castSucc)) =
            U.oneLift H r.1
              (TreeLevel (T := T) (U.cut r.1)) := by
        have hVcut0 : V.cut r.castSucc = U.cut r.1 := by
          rw [hcut r.castSucc, hidx0]
          rfl
        rw [hVcut0]
        rw [← hVone, hVprefix, hxone]
      have htarget :
          Z.liftTo H (idx r.castSucc) (idx r.succ)
              (le_of_lt (hidxStrict (by
                change r.1 < r.1 + 1
                omega)))
              (TreeLevel (T := T) (Z.cut (idx r.castSucc))) =
            U.oneLift H r.1
              (TreeLevel (T := T) (U.cut r.1)) := by
        rw [hidx0, hidx1]
        have hseg :=
          U.initialSegment_liftTo H (a + i + 1)
            (⟨r.1, by omega⟩ : Fin (a + i + 2))
            (⟨r.1 + 1, by omega⟩ : Fin (a + i + 2))
            (by omega)
            (TreeLevel (T := T) (U.cut r.1))
        change
          Z.liftTo H
              (⟨r.1, by omega⟩ : Fin (Z.height + 1))
              (⟨r.1 + 1, by omega⟩ : Fin (Z.height + 1))
              _
              (TreeLevel (T := T) (U.cut r.1)) =
            _
        rw [hseg]
        exact U.liftTo_succ H r.1
          (TreeLevel (T := T) (U.cut r.1))
      rw [hsource, htarget]
    · have hre : r.1 = a := by
        have hrbound : r.1 < a + 1 := by
          simpa [V, hVheight] using r.2
        omega
      have hrLast : r = Fin.last x.height := by
        apply Fin.ext
        simpa [x, hxheight] using hre
      have hidx0 :
          idx r.castSucc =
            (⟨a, by omega⟩ : Fin (Z.height + 1)) := by
        apply Fin.ext
        simp [idx, hre]
      have hidx1 :
          idx r.succ =
            Fin.last Z.height := by
        apply Fin.ext
        simp [idx, hre, hZheight]
      have hsource :
          V.oneLift H r
              (TreeLevel (T := T) (V.cut r.castSucc)) =
            H.canonicalExtension
                ((headRow H U a i P).representative H)
                (U.cut a) ''
              ImmediateSuccessors (T := T)
                (TreeLevel (T := T) (U.cut a)) := by
        have hVcut0 : V.cut r.castSucc = U.cut a := by
          rw [hcut r.castSucc, hidx0]
          rfl
        rw [hVcut0]
        dsimp [V, h]
        rw [hrLast]
        simpa [x] using
          FiniteFatTree.appendRow_oneLift_last H x
            (headRow H U a i P)
            (TreeLevel (T := T) (U.cut a))
      have htarget :
          Z.liftTo H (idx r.castSucc) (idx r.succ)
              (le_of_lt (hidxStrict (by
                change r.1 < r.1 + 1
                omega)))
              (TreeLevel (T := T) (Z.cut (idx r.castSucc))) =
            U.liftTo H a (a + i + 1) (by omega)
              (TreeLevel (T := T) (U.cut a)) := by
        rw [hidx0, hidx1]
        simpa [Z, hZheight] using
          U.initialSegment_liftTo H (a + i + 1)
            (⟨a, by omega⟩ : Fin (a + i + 2))
            (Fin.last (a + i + 1))
            (by omega)
            (TreeLevel (T := T) (U.cut a))
      rw [hsource, htarget]
      exact headRow_oneLift_subset H U a i P

  unfold StemAt
  refine ⟨?_, ?_⟩
  · exact ⟨{
      index := idx
      index_strict := hidxStrict
      cut_eq := hcut
      lift_subset := hlift
    }⟩
  · change V.terminalCut = Z.terminalCut
    have hlastV : V.cut (Fin.last V.height) =
        Z.cut (idx (Fin.last V.height)) :=
      hcut (Fin.last V.height)
    have hidxLast :
        idx (Fin.last V.height) = Fin.last Z.height := by
      apply Fin.ext
      simp [idx, hVheight, hZheight]
    simpa [FiniteFatTree.terminalCut, hidxLast] using hlastV

end TraceHistoryState
end FatTree
end SMTree
end SuccessorTree
