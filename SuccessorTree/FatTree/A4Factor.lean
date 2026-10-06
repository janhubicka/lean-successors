import SuccessorTree.FatTree.A4Profiles

/-!
# Last-block factorization for fat-tree A4

The all-trace A4 fusion must cover arbitrary geometric one-block reductions,
not only canonical right-compositions. Every such last block factors through
an exact trace of the preceding finite prefix and the ambient last row as soon
as every node on the source cut has an immediate successor.  This is the
actual geometric hypothesis used by the proof.  M3 supplies it at every
positive cut, while a root letter supplies it at cut zero.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Exact agreement of an infinite fat tree with one of its own prefixes. -/
theorem initialSegment_extendsStem (U : FatTree H) (n : Nat) :
    ExtendsStem H (U.initialSegment H n) U := by
  apply extendsStem_of_initialSegment_eq H
  rfl

/-- Last-block factorization.

Suppose `y` is literally the initial stem of `U`, and a row `g` appended
to `y` occurs at depth `m+1` in `U`.  Then `g` factors through an
exact trace from the terminal cut of `y` to cut `m`, followed by the
ambient row `U.row m`.

The equality is heterogeneous only because the exact-trace source cut is
definitionally `U.cut y.height`, whereas `g` is indexed by
`y.terminalCut`; exact stem agreement identifies these cuts. -/
theorem exists_lastBlock_exactTrace_of_successors
    (y : FiniteFatTree H)
    (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (hsuccessors :
      ∀ x : T, LevelTree.lev x = y.terminalCut → ∃ z : T, x ⋖ z)
    (m : Nat) (hym : y.height ≤ m)
    (g : AM H y.terminalCut 1)
    (hg :
      StemAt H (FiniteFatTree.appendRow H y g) U (m + 1)) :
    ∃ p : FiniteFatTree.ExactTrace H
        (U.initialSegment H m) y.height hym,
      HEq g
        (H.composeAcross
          (exactTraceToAMExact H (U.initialSegment H m)
            y.height hym p)
          (U.row m)) := by
  classical
  let V : FiniteFatTree H := FiniteFatTree.appendRow H y g
  let Z : FiniteFatTree H := U.initialSegment H (m + 1)
  rcases hg.1 with ⟨w⟩

  let irow : Fin V.height := ⟨y.height, by
    change y.height < y.height + 1
    omega⟩
  let j0 : Fin (Z.height + 1) := ⟨y.height, by
    change y.height < (m + 1) + 1
    omega⟩
  let jmid : Fin (Z.height + 1) := ⟨m, by
    change m < (m + 1) + 1
    omega⟩
  let jrow : Fin Z.height := ⟨m, by
    change m < m + 1
    omega⟩

  have hirow : irow = Fin.last y.height := by
    apply Fin.ext
    rfl
  have hirowSucc : irow.succ = Fin.last V.height := by
    apply Fin.ext
    rfl
  have hjmid : jmid = jrow.castSucc := by
    apply Fin.ext
    rfl
  have hjlast : Fin.last Z.height = jrow.succ := by
    apply Fin.ext
    rfl

  have hVcut :
      V.cut irow.castSucc = y.terminalCut := by
    rw [hirow]
    dsimp [V]
    exact FiniteFatTree.appendRow_cut_old H y g (Fin.last y.height)

  have hidx0 : w.index irow.castSucc = j0 := by
    apply Fin.ext
    apply U.cut_injective H
    calc
      U.cut (w.index irow.castSucc).1 =
          Z.cut (w.index irow.castSucc) := rfl
      _ = V.cut irow.castSucc := (w.cut_eq irow.castSucc).symm
      _ = y.terminalCut := hVcut
      _ = U.cut y.height :=
        (terminalCut_eq_of_extendsStem H hyU).symm
      _ = U.cut j0.1 := rfl

  have hidxLast :
      w.index (Fin.last V.height) = Fin.last Z.height :=
    w.index_last_eq_last H hg.2

  have hsrc :
      FiniteFatTree.traceSourceCut H (U.initialSegment H m)
          y.height hym =
        y.terminalCut := by
    change U.cut y.height = y.terminalCut
    exact terminalCut_eq_of_extendsStem H hyU

  have hcd : y.terminalCut ≤ U.cut m := by
    calc
      y.terminalCut = U.cut y.height :=
        (terminalCut_eq_of_extendsStem H hyU).symm
      _ ≤ U.cut m := (U.cut_strictMono H).monotone hym

  have hVterm :
      V.terminalCut = U.cut (m + 1) := by
    calc
      V.terminalCut = Z.terminalCut := hg.2
      _ = U.cut (m + 1) := rfl

  have hgend :
      g.rowEndLevel H = (U.row m).rowEndLevel H := by
    have hgterm :
        g.rowEndLevel H + 1 = U.cut (m + 1) := by
      calc
        g.rowEndLevel H + 1 =
            (FiniteFatTree.appendRow H y g).terminalCut :=
          (FiniteFatTree.appendRow_terminalCut H y g).symm
        _ = V.terminalCut := rfl
        _ = U.cut (m + 1) := hVterm
    have hUterm := U.row_cut m
    omega

  have hdt : U.cut m ≤ g.topLevel H := by
    change U.cut m ≤ g.rowEndLevel H
    rw [hgend]
    exact H.levelMap_id_le (U.row m).representative.map (U.cut m)

  obtain ⟨prow, hptop, hple⟩ :=
    exists_truncate_oneRow H g (U.cut m) hcd hdt
  change prow.rowEndLevel H = U.cut m at hptop

  let pcast : AM H
      (FiniteFatTree.traceSourceCut H (U.initialSegment H m)
        y.height hym) 1 :=
    FiniteFatTree.castTraceRow H hsrc.symm prow

  have hpEnd :
      pcast.rowEndLevel H =
        FiniteFatTree.traceTargetCut H (U.initialSegment H m) := by
    calc
      pcast.rowEndLevel H = prow.rowEndLevel H := by
        simp [pcast]
      _ = U.cut m := hptop
      _ = FiniteFatTree.traceTargetCut H (U.initialSegment H m) := rfl

  have hrowExt :
      V.rowExtension H irow =
        H.canonicalExtension (g.representative H) y.terminalCut := by
    rw [hirow]
    dsimp [V]
    exact FiniteFatTree.appendRow_rowExtension_last H y g

  have hLift := w.lift_subset irow

  have hpoint :
      ∀ (x : T),
        LevelTree.lev x =
            FiniteFatTree.traceSourceCut H (U.initialSegment H m)
              y.height hym →
          pcast.representative H x ∈
              FiniteFatTree.traceLift H (U.initialSegment H m)
                y.height hym ∧
          (U.row m).representative H (pcast.representative H x) =
            g.representative H x := by
    intro x hx
    have hxy : LevelTree.lev x = y.terminalCut :=
      hx.trans hsrc

    rcases hsuccessors x hxy with ⟨b, hxb⟩
    have hbmem :
        b ∈ ImmediateSuccessors (T := T)
          (TreeLevel (T := T) (V.cut irow.castSucc)) := by
      refine ⟨x, ?_, hxb⟩
      rw [hVcut]
      exact hxy

    let zlast : T := V.rowExtension H irow b
    have hzV :
        zlast ∈ V.oneLift H irow
          (TreeLevel (T := T) (V.cut irow.castSucc)) :=
      ⟨b, hbmem, rfl⟩
    have hzZ := hLift hzV
    have hidxSucc :
        w.index irow.succ = Fin.last Z.height := by
      rw [hirowSucc]
      exact hidxLast
    change
      zlast ∈ Z.liftTo H
        (w.index irow.castSucc) (w.index irow.succ) _
        (TreeLevel (T := T) (Z.cut (w.index irow.castSucc))) at hzZ
    have hOld :
        w.index irow.castSucc ≤ w.index irow.succ := by
      exact le_of_lt (w.index_strict (by
        change irow.1 < irow.1 + 1
        omega))
    have hNew : j0 ≤ Fin.last Z.height :=
      Fin.le_last j0
    have hLiftCongr :=
      Z.liftTo_congr H hOld hNew hidx0 hidxSucc
        (TreeLevel (T := T) (Z.cut (w.index irow.castSucc)))
    have hzZ' :
        zlast ∈ Z.liftTo H j0 (Fin.last Z.height) hNew
          (TreeLevel (T := T) (Z.cut j0)) := by
      have hz0 := hzZ
      rw [hLiftCongr] at hz0
      simpa [hidx0] using hz0

    have h0m : j0 ≤ jmid := by
      change y.height ≤ m
      exact hym
    have hmLast : jmid ≤ Fin.last Z.height := by
      change m ≤ m + 1
      omega
    let X0 : Set T := TreeLevel (T := T) (Z.cut j0)
    let Y0 : Set T := Z.liftTo H j0 jmid h0m X0
    have hsplit :=
      Z.liftTo_split H j0 jmid (Fin.last Z.height)
        h0m hmLast X0
    have hzSplit :
        zlast ∈ Z.liftTo H jmid (Fin.last Z.height) hmLast Y0 := by
      have hmem :=
        congrArg (fun W : Set T => zlast ∈ W) hsplit
      exact hmem.mp (by simpa [X0] using hzZ')
    have hAdj : jrow.castSucc ≤ jrow.succ := by
      change jrow.1 ≤ jrow.1 + 1
      omega
    have hOuterCongr :=
      Z.liftTo_congr H hmLast hAdj hjmid hjlast Y0
    have hzAdj :
        zlast ∈ Z.liftTo H jrow.castSucc jrow.succ hAdj Y0 := by
      have hmem :=
        congrArg (fun W : Set T => zlast ∈ W) hOuterCongr
      exact hmem.mp hzSplit
    have hOneEq := Z.liftTo_succ H jrow Y0
    have hzOne : zlast ∈ Z.oneLift H jrow Y0 := by
      have hmem :=
        congrArg (fun W : Set T => zlast ∈ W) hOneEq
      exact hmem.mp hzAdj

    rcases hzOne with ⟨s, hs, hzs⟩
    rcases hs with ⟨t, ht, hts⟩

    have hInterLevel :
        Z.liftTo H j0 jmid h0m
            (TreeLevel (T := T) (Z.cut j0)) ⊆
          TreeLevel (T := T) (Z.cut jmid) := by
      apply Z.liftTo_subset_level H
      intro a ha
      exact ha
    have htLevel : LevelTree.lev t = U.cut m := by
      have htZ := hInterLevel ht
      change LevelTree.lev t = Z.cut jmid at htZ
      have hZmid : Z.cut jmid = U.cut m := by
        rfl
      exact htZ.trans hZmid

    have hpLeG :
        pcast.representative H x ≤ g.representative H x := by
      have hp0 := hple x hxy
      simpa [pcast] using hp0

    have hgLeLast :
        g.representative H x ≤ zlast := by
      have hrowx :
          V.rowExtension H irow x = g.representative H x := by
        rw [hrowExt]
        exact H.canonicalExtension_agrees
          (g.representative H) y.terminalCut x (by omega)
      have hmap :
          V.rowExtension H irow x ≤ V.rowExtension H irow b :=
        (V.rowExtension H irow).map.map_le_of_le hxb.le
      simpa [zlast, hrowx] using hmap

    have htCut : LevelTree.lev t = Z.cut jrow.castSucc := by
      have hZrow : Z.cut jrow.castSucc = U.cut m := by
        rfl
      exact htLevel.trans hZrow.symm
    have htRow :
        t ≤ Z.rowExtension H jrow t :=
      Z.le_rowExtension_at_cut H jrow htCut
    have hrowMono :
        Z.rowExtension H jrow t ≤ Z.rowExtension H jrow s :=
      (Z.rowExtension H jrow).map.map_le_of_le hts.le
    have htLeLast : t ≤ zlast := by
      calc
        t ≤ Z.rowExtension H jrow t := htRow
        _ ≤ Z.rowExtension H jrow s := hrowMono
        _ = zlast := hzs

    have hpLevel :
        LevelTree.lev (pcast.representative H x) = U.cut m := by
      calc
        LevelTree.lev (pcast.representative H x) =
            H.levelMap (pcast.representative H).map
              (LevelTree.lev x) :=
          (H.levelMap_eq (pcast.representative H).map (a := x)).symm
        _ = H.levelMap (pcast.representative H).map
              (FiniteFatTree.traceSourceCut H (U.initialSegment H m)
                y.height hym) := by rw [hx]
        _ = pcast.rowEndLevel H := rfl
        _ = prow.rowEndLevel H := by simp [pcast]
        _ = U.cut m := hptop

    have hpLeLast :
        pcast.representative H x ≤ zlast :=
      hpLeG.trans hgLeLast
    have hpt :
        pcast.representative H x = t := by
      rcases LevelTree.comparable_below hpLeLast htLeLast with h | h
      · exact LevelTree.same_level_of_le h
          (hpLevel.trans htLevel.symm)
      · exact (LevelTree.same_level_of_le h
          (htLevel.trans hpLevel.symm)).symm

    have htU :
        t ∈ U.liftTo H y.height m hym
          (TreeLevel (T := T) (U.cut y.height)) := by
      have hseg :=
        U.initialSegment_liftTo H (m + 1)
          j0 jmid h0m (TreeLevel (T := T) (Z.cut j0))
      change
        t ∈ Z.liftTo H j0 jmid h0m
          (TreeLevel (T := T) (Z.cut j0)) at ht
      rw [hseg] at ht
      have hZ0 : Z.cut j0 = U.cut y.height := by
        rfl
      change
        t ∈ U.liftTo H y.height m hym
          (TreeLevel (T := T) (U.cut y.height))
      simpa only [hZ0] using ht

    have hpTrace :
        pcast.representative H x ∈
          FiniteFatTree.traceLift H (U.initialSegment H m)
            y.height hym := by
      rw [hpt]
      unfold FiniteFatTree.traceLift
      rw [U.initialSegment_liftTo H m]
      change
        t ∈ U.liftTo H y.height m hym
          (TreeLevel (T := T) (U.cut y.height))
      exact htU

    have hrowTLeLast :
        Z.rowExtension H jrow t ≤ zlast := by
      calc
        Z.rowExtension H jrow t ≤ Z.rowExtension H jrow s := hrowMono
        _ = zlast := hzs

    have hUrowT :
        Z.rowExtension H jrow t =
          (U.row m).representative H t := by
      calc
        Z.rowExtension H jrow t =
            U.rowExtension H m t := by
          rw [U.initialSegment_rowExtension H (m + 1) jrow]
        _ = (U.row m).representative H t :=
          U.rowExtension_agrees H m t (by
            exact Nat.le_of_eq htLevel)

    have hUrowLevel :
        LevelTree.lev ((U.row m).representative H t) =
          g.rowEndLevel H := by
      calc
        LevelTree.lev ((U.row m).representative H t) =
            H.levelMap (U.row m).representative.map (LevelTree.lev t) :=
          (H.levelMap_eq (U.row m).representative.map (a := t)).symm
        _ = H.levelMap (U.row m).representative.map (U.cut m) := by
          rw [htLevel]
        _ = (U.row m).rowEndLevel H := rfl
        _ = g.rowEndLevel H := hgend.symm

    have hgLevel :
        LevelTree.lev (g.representative H x) =
          g.rowEndLevel H := by
      calc
        LevelTree.lev (g.representative H x) =
            H.levelMap (g.representative H).map (LevelTree.lev x) :=
          (H.levelMap_eq (g.representative H).map (a := x)).symm
        _ = H.levelMap (g.representative H).map y.terminalCut := by
          rw [hxy]
        _ = g.rowEndLevel H := rfl

    have hUrowLeLast :
        (U.row m).representative H t ≤ zlast := by
      rw [← hUrowT]
      exact hrowTLeLast

    have hfactorT :
        (U.row m).representative H t =
          g.representative H x := by
      rcases LevelTree.comparable_below hUrowLeLast hgLeLast with h | h
      · exact LevelTree.same_level_of_le h
          (hUrowLevel.trans hgLevel.symm)
      · exact (LevelTree.same_level_of_le h
          (hgLevel.trans hUrowLevel.symm)).symm

    refine ⟨hpTrace, ?_⟩
    rw [hpt]
    exact hfactorT

  have hpExact :
      FiniteFatTree.IsExactTrace H (U.initialSegment H m)
        y.height hym pcast := by
    refine ⟨hpEnd, ?_⟩
    intro x hx
    exact (hpoint x hx).1

  let p : FiniteFatTree.ExactTrace H
      (U.initialSegment H m) y.height hym :=
    ⟨pcast, hpExact⟩
  refine ⟨p, ?_⟩

  let comp : AM H
      (FiniteFatTree.traceSourceCut H (U.initialSegment H m)
        y.height hym) 1 :=
    H.composeAcross
      (exactTraceToAMExact H (U.initialSegment H m)
        y.height hym p)
      (U.row m)
  let compCast : AM H y.terminalCut 1 :=
    FiniteFatTree.castTraceRow H hsrc comp

  have hrep :
      ∀ (x : T), LevelTree.lev x ≤ y.terminalCut →
        g.representative H x = compCast.representative H x := by
    intro x hx
    have hcomp :
        comp.representative H x =
          (U.row m).representative H (p.1.representative H x) := by
      exact H.composeAcross_representative_agrees
        (exactTraceToAMExact H (U.initialSegment H m)
          y.height hym p)
        (U.row m) x (by
          rw [hsrc]
          exact hx)
    have hcast :
        compCast.representative H x = comp.representative H x := by
      simp [compCast]
    by_cases hlt : LevelTree.lev x < y.terminalCut
    · have hgfix : g.representative H x = x :=
        g.representative_fixesBelow H x hlt
      have hpfix : p.1.representative H x = x := by
        apply p.1.representative_fixesBelow H x
        rw [hsrc]
        exact hlt
      have hUfix :
          (U.row m).representative H x = x := by
        apply (U.row m).representative_fixesBelow H x
        exact lt_of_lt_of_le hlt hcd
      rw [hcast, hcomp, hpfix, hUfix, hgfix]
    · have hxeq : LevelTree.lev x = y.terminalCut := by omega
      have hxsrc :
          LevelTree.lev x =
            FiniteFatTree.traceSourceCut H (U.initialSegment H m)
              y.height hym := by
        exact hxeq.trans hsrc.symm
      have hfac := (hpoint x hxsrc).2
      rw [hcast, hcomp]
      exact hfac.symm

  have hEq : g = compCast := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hgTop := congrArg Subtype.val (g.representative_top H)
    have hcTop := congrArg Subtype.val (compCast.representative_top H)
    change
      (g.representative H).restrictLe H y.terminalCut = g.1.1 at hgTop
    change
      (compCast.representative H).restrictLe H y.terminalCut =
        compCast.1.1 at hcTop
    calc
      g.1.1 x = g.representative H x.1 :=
        (congrFun hgTop x).symm
      _ = compCast.representative H x.1 :=
        hrep x.1 x.2
      _ = compCast.1.1 x :=
        congrFun hcTop x

  have hcastHEq :
      HEq compCast comp := by
    change HEq (FiniteFatTree.castTraceRow H hsrc comp) comp
    exact FiniteFatTree.castTraceRow_heq H hsrc comp
  have hEqHEq : HEq g compCast := by
    rw [hEq]
  exact hEqHEq.trans hcastHEq

/-- A one-level letter on the source cut supplies the successor hypothesis
needed by last-block factorisation, including at cut zero. -/
theorem exists_lastBlock_exactTrace_of_sourceLetter
    (y : FiniteFatTree H)
    (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (E : OneLevelLetter H y.terminalCut)
    (m : Nat) (hym : y.height ≤ m)
    (g : AM H y.terminalCut 1)
    (hg :
      StemAt H (FiniteFatTree.appendRow H y g) U (m + 1)) :
    ∃ p : FiniteFatTree.ExactTrace H
        (U.initialSegment H m) y.height hym,
      HEq g
        (H.composeAcross
          (exactTraceToAMExact H (U.initialSegment H m)
            y.height hym p)
          (U.row m)) := by
  apply exists_lastBlock_exactTrace_of_successors H y U hyU
    (fun x hx => ⟨E.toMMap x, H.letter_covBy E hx⟩)
    m hym g hg

/-- Positive source cuts satisfy the successor hypothesis by M3.  This
compatibility wrapper retains the original interface used by the existing
positive-cut development. -/
theorem exists_lastBlock_exactTrace
    (y : FiniteFatTree H)
    (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (hsourcePos : 0 < y.terminalCut)
    (m : Nat) (hym : y.height ≤ m)
    (g : AM H y.terminalCut 1)
    (hg :
      StemAt H (FiniteFatTree.appendRow H y g) U (m + 1)) :
    ∃ p : FiniteFatTree.ExactTrace H
        (U.initialSegment H m) y.height hym,
      HEq g
        (H.composeAcross
          (exactTraceToAMExact H (U.initialSegment H m)
            y.height hym p)
          (U.row m)) := by
  exact exists_lastBlock_exactTrace_of_sourceLetter H y U hyU
    (duplicateHistoryLetter H 0 y.terminalCut hsourcePos)
    m hym g hg

end FatTree
end SMTree
end SuccessorTree
