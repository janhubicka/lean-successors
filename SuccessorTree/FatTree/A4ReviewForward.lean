import SuccessorTree.FatTree.A4ReviewReplay

/-!
# Forward M2 and saturation of all raw successor fans

The finite raw fan need not be admissible. Only its image under the canonical
head is assumed admissible. Compose that image FORWARDS with a transported
replay letter, extract the resulting one-level letter by M2, and use global
saturation. This is the forward argument in the review's `trace-profiles`
lemma; no inverse closure of the monoid is used.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

private theorem forward_map_fixed {A : Type*} (f : A → A) (xs : List A)
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, hx, ih hxs]

/-- Extract an admissible letter from an admissible map and its actual
predecessors. The predecessor table is not assumed to be an M-map. -/
theorem review_letter_for_admissible_successors
    (c b : Nat) (hcb : c ≤ b) (F : MMap H)
    (hfix : F.FixesBelow H c) (htop : H.levelMap F.map c = b + 1)
    (p : T → T)
    (hpLevel : ∀ x : T, LevelTree.lev x = c → LevelTree.lev (p x) = b)
    (hpBelow : ∀ x : T, LevelTree.lev x = c → p x ≤ F x) :
    ∃ E : OneLevelLetter H b,
      ∀ x : T, LevelTree.lev x = c → E.toMMap (p x) = F x := by
  have hcut : SplitCut H F c b := by
    constructor
    · rw [htop]; omega
    · cases c with
      | zero => trivial
      | succ k =>
          change H.levelMap F.map k < b
          obtain ⟨z, hz⟩ := H.level_nonempty k
          have hFz : F z = z := hfix z (by omega)
          have hFk : H.levelMap F.map k = k := by
            calc
              H.levelMap F.map k = LevelTree.lev (F z) := by
                simpa only [hz] using H.levelMap_eq F.map (a := z)
              _ = k := by rw [hFz, hz]
          rw [hFk]
          omega
  obtain ⟨G, D, _, hGtop, hDfix, hDG⟩ := H.exists_shapeSplit_factor F c b hcut
  have hGlevel (x : T) (hx : LevelTree.lev x = c) :
      LevelTree.lev (G x) = b := by
    calc
      LevelTree.lev (G x) = H.levelMap G.map (LevelTree.lev x) :=
        (H.levelMap_eq G.map (a := x)).symm
      _ = b := by rw [hx, hGtop]
  have hDtop : H.levelMap D.map b = b + 1 := by
    obtain ⟨x, hx⟩ := H.level_nonempty c
    calc
      H.levelMap D.map b = LevelTree.lev (D (G x)) := by
        simpa only [hGlevel x hx] using H.levelMap_eq D.map (a := G x)
      _ = LevelTree.lev (F x) := congrArg LevelTree.lev (hDG x (Nat.le_of_eq hx))
      _ = H.levelMap F.map c := by
        simpa only [hx] using (H.levelMap_eq F.map (a := x)).symm
      _ = b + 1 := htop
  let E : OneLevelLetter H b :=
    ⟨H.canonicalExtension D b, H.canonicalExtension_skipsOnly_of_oneStep D b hDfix hDtop⟩
  refine ⟨E, ?_⟩
  intro x hx
  have hGbelow : G x ≤ F x := by
    have h := MMap.le_apply_at_cut H D b hDfix (hGlevel x hx)
    rwa [hDG x (Nat.le_of_eq hx)] at h
  have hGp : G x = p x := by
    rcases LevelTree.comparable_below hGbelow (hpBelow x hx) with h | h
    · exact LevelTree.same_level_of_le h ((hGlevel x hx).trans (hpLevel x hx).symm)
    · exact (LevelTree.same_level_of_le h ((hpLevel x hx).trans (hGlevel x hx).symm)).symm
  calc
    E.toMMap (p x) = D (p x) :=
      H.canonicalExtension_agrees D b (p x) (Nat.le_of_eq (hpLevel x hx))
    _ = D (G x) := congrArg D hGp.symm
    _ = F x := hDG x (Nat.le_of_eq hx)

namespace ProfileReplayState

variable {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
variable (U : FatTree H) (a : Nat) (trace : C → AM H c 1)
variable (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
variable (K : ProfileCollector H U a trace)

omit [Fintype C] [Nonempty C] in
include hend in
private theorem forward_trace_level
    (j : C) (x : T) (hx : LevelTree.lev x = c) :
    LevelTree.lev ((trace j).representative H x) = U.cut a := by
  calc
    LevelTree.lev ((trace j).representative H x) =
        H.levelMap ((trace j).representative H).map (LevelTree.lev x) :=
      (H.levelMap_eq ((trace j).representative H).map (a := x)).symm
    _ = (trace j).rowEndLevel H := by rw [hx]; rfl
    _ = U.cut a := hend j

/-- An admissible full successor image at a reachable history produces an
actual seen profile by M2 and global saturation. The raw fan itself is not
required to be admissible. -/
omit [Nonempty C] in
theorem review_seen_of_admissible_successors
    (hglobal : ProfileCollector.GloballySaturated H U a trace hend K)
    (R : ProfileReplayState H U a trace hend K) (j : C)
    (e : RawSuccessorFan H (trace j)) (F : MMap H)
    (hfix : F.FixesBelow H c)
    (htop : H.levelMap F.map c = U.cut (a + R.collector.index) + 1)
    (hedge : ∀ (x : InitialNode T c) (hx : LevelTree.lev x.1 = c),
      S.succ (R.collector.state ((trace j).representative H x.1))
        (e.code H x hx).params (e.code H x hx).char = some (F x.1)) :
    ∃ alpha : SeenProfile H K, alpha.1 j = some e := by
  have hcd : c ≤ U.cut a := by
    exact (H.levelMap_id_le ((trace j).representative H).map c).trans_eq (hend j)
  have hcm : c ≤ U.cut (a + R.collector.index) :=
    hcd.trans ((U.cut_strictMono H).monotone (by omega))
  let p := fun x => R.collector.state ((trace j).representative H x)
  have hplevel : ∀ x : T, LevelTree.lev x = c →
      LevelTree.lev (p x) = U.cut (a + R.collector.index) := by
    intro x hx
    exact R.collector.state.level_apply H U a R.collector.index
      (forward_trace_level H U a trace hend j x hx)
  have hpbelow : ∀ x : T, LevelTree.lev x = c → p x ≤ F x := by
    intro x hx
    exact (S.covBy_of_succ_eq_some (hedge ⟨x, Nat.le_of_eq hx⟩ hx)).le
  obtain ⟨E, hE⟩ := review_letter_for_admissible_successors H c
    (U.cut (a + R.collector.index)) hcm F hfix htop p hplevel hpbelow
  have hreal : HistoryRealizesFan H (trace j) R.collector.state.toMMap E e := by
    intro x hx
    exact (hedge x hx).trans (congrArg some (hE x.1 hx).symm)
  let alpha := ProfileCollector.currentProfile H U a trace R.collector E
  have hmem : alpha ∈ K.seen :=
    ProfileCollector.currentProfile_mem_start H hend hglobal R.reachable E
  exact ⟨⟨alpha, hmem⟩,
    historyProfile_eq_some H (trace j) R.collector.state.toMMap E e hreal⟩

/-- The canonical head transports every raw fan edge with its actual code.
This is a pointwise statement and does not assert that the fan is admissible. -/
omit [Nonempty C] in
theorem review_head_raw_fan_edge
    (R : ProfileReplayState H U a trace hend K) (j : C)
    (e : RawSuccessorFan H (trace j))
    (x : InitialNode T c) (hx : LevelTree.lev x.1 = c) :
    let h := TraceHistoryState.headRow H U a R.collector.index R.collector.state
    S.succ (h.representative H ((trace j).representative H x.1))
      (e.code H x hx).params (e.code H x hx).char =
      some (H.canonicalExtension (h.representative H) (U.cut a) (e.toFun x).1) := by
  dsimp only
  let h := TraceHistoryState.headRow H U a R.collector.index R.collector.state
  let A := H.canonicalExtension (h.representative H) (U.cut a)
  let qx := (trace j).representative H x.1
  let code := e.code H x hx
  have hq : LevelTree.lev qx = U.cut a := forward_trace_level H U a trace hend j x.1 hx
  have he : LevelTree.lev (e.toFun x).1 = U.cut a + 1 :=
    (LevelTree.covBy_level_eq (e.top_covBy x hx)).trans (congrArg (fun n => n + 1) hq)
  have hconsecutive : H.levelMap A.map (LevelTree.lev (e.toFun x).1) =
      H.levelMap A.map (LevelTree.lev qx) + 1 := by
    rw [he, hq]
    exact H.canonicalExtension_level_succ (h.representative H) (U.cut a) (U.cut a) le_rfl
  have hparams : code.params.map A.map = code.params := by
    apply forward_map_fixed
    intro p hp
    have hplt : LevelTree.lev p < U.cut a :=
      (S.parameter_level_lt code.succ_eq hp).trans_eq hq
    exact (H.canonicalExtension_agrees (h.representative H) (U.cut a) p
      (Nat.le_of_lt hplt)).trans (h.representative_fixesBelow H p hplt)
  have hedge := H.succ_eq_of_consecutive_levels A.map code.succ_eq hconsecutive
  rw [hparams, H.canonicalExtension_agrees (h.representative H) (U.cut a) qx
    (Nat.le_of_eq hq)] at hedge
  exact hedge

/-- Every admissible image of a raw fan under the first head is already
represented by a seen profile. A transported replay letter supplies the
forward composite; M2 extracts a legitimate next history letter.

The conclusion includes the actual pointwise representation by a replayed
first-parameter step, not just membership of a profile in the alphabet. -/
theorem review_raw_fan_represented
    (hglobal : ProfileCollector.GloballySaturated H U a trace hend K)
    (R : ProfileReplayState H U a trace hend K) (alpha0 : SeenProfile H K)
    (j : C) (e : RawSuccessorFan H (trace j))
    (theta : AM H c 1)
    (htheta : theta.rowEndLevel H = U.cut (firstParameterIndex H R + 1))
    (hraw : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
      theta.representative H x.1 =
        H.canonicalExtension
          ((TraceHistoryState.headRow H U a R.collector.index R.collector.state).representative H)
          (U.cut a) (e.toFun x).1) :
    ∃ alpha : SeenProfile H K, alpha.1 j = some e ∧
      ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
        theta.representative H x.1 =
          (step H U a trace hend K R alpha).collector.state
            ((trace j).representative H x.1) := by
  let J := firstParameterIndex H R
  let ell := (U.row J).rowEndLevel H
  let b := U.cut (J + 1)
  let h := TraceHistoryState.headRow H U a R.collector.index R.collector.state
  let E0 := replayLetter H U a trace hend K R alpha0
  let D0 := rowTransportLetter H U J E0
  let D := D0.toMMap
  let Rnext := step H U a trace hend K R alpha0
  have hellb : ell + 1 = b := U.row_cut J
  have hdell : U.cut a ≤ ell := by
    have htop := TraceHistoryState.headRow_rowEndLevel H U a R.collector.index R.collector.state
    exact (H.levelMap_id_le (h.representative H).map (U.cut a)).trans_eq htop
  have hcd : c ≤ U.cut a :=
    (H.levelMap_id_le ((trace j).representative H).map c).trans_eq (hend j)
  have hDtop : H.levelMap D.map b = b + 1 := by
    rw [← hellb]
    simp [D, H.levelMap_of_skipsOnly D0.toMMap.map ell D0.skips]
  let F := MMap.comp H D (theta.representative H)
  have hFfix : F.FixesBelow H c := by
    intro x hx
    change D (theta.representative H x) = x
    rw [theta.representative_fixesBelow H x hx]
    exact D0.eq_id_below H (hx.trans_le (hcd.trans hdell))
  have hFtop : H.levelMap F.map c = U.cut (a + Rnext.collector.index) + 1 := by
    rw [H.levelMap_comp D (theta.representative H) c]
    change H.levelMap D.map (theta.rowEndLevel H) = _
    rw [htheta, hDtop]
    rfl
  have hedge : ∀ (x : InitialNode T c) (hx : LevelTree.lev x.1 = c),
      S.succ (Rnext.collector.state ((trace j).representative H x.1))
        (e.code H x hx).params (e.code H x hx).char = some (F x.1) := by
    intro x hx
    let qx := (trace j).representative H x.1
    let code := e.code H x hx
    have hq : LevelTree.lev qx = U.cut a :=
      forward_trace_level H U a trace hend j x.1 hx
    have hhead : S.succ (h.representative H qx) code.params code.char =
        some (theta.representative H x.1) := by
      rw [hraw x hx]
      exact review_head_raw_fan_edge H U a trace hend K R j e x hx
    have hheadLevel : LevelTree.lev (h.representative H qx) = ell := by
      calc
        LevelTree.lev (h.representative H qx) =
            H.levelMap (h.representative H).map (LevelTree.lev qx) :=
          (H.levelMap_eq (h.representative H).map (a := qx)).symm
        _ = h.rowEndLevel H := by rw [hq]; rfl
        _ = ell := TraceHistoryState.headRow_rowEndLevel H U a R.collector.index R.collector.state
    have hthetaLevel : LevelTree.lev (theta.representative H x.1) = ell + 1 :=
      (LevelTree.covBy_level_eq (S.covBy_of_succ_eq_some hhead)).trans
        (congrArg (fun n => n + 1) hheadLevel)
    have hconsecutive : H.levelMap D.map (LevelTree.lev (theta.representative H x.1)) =
        H.levelMap D.map (LevelTree.lev (h.representative H qx)) + 1 := by
      rw [hthetaLevel, hheadLevel]
      simp [D, H.levelMap_of_skipsOnly D0.toMMap.map ell D0.skips]
    have hparams : code.params.map D.map = code.params := by
      apply forward_map_fixed
      intro p hp
      exact D0.eq_id_below H
        (((S.parameter_level_lt code.succ_eq hp).trans_eq hq).trans_le hdell)
    have htrans := H.succ_eq_of_consecutive_levels D.map hhead hconsecutive
    rw [hparams] at htrans
    have hDhead : D (h.representative H qx) = Rnext.collector.state qx := by
      rw [TraceHistoryState.headRow_representative_eq_rowExtension H U a
        R.collector.index R.collector.state qx (Nat.le_of_eq hq)]
      have hcur := R.collector.state.level_apply H U a R.collector.index hq
      exact (rowTransportLetter_commutes H U J E0 (R.collector.state qx)
        (Nat.le_of_eq hcur)).trans
        (step_state_apply H U a trace hend K R alpha0 qx).symm
    rw [hDhead] at htrans
    exact htrans
  obtain ⟨alpha, halpha⟩ := review_seen_of_admissible_successors H U a trace hend K
    hglobal Rnext j e F hFfix hFtop hedge
  refine ⟨alpha, halpha, ?_⟩
  intro x hx
  let qx := (trace j).representative H x.1
  have hq : LevelTree.lev qx = U.cut a := forward_trace_level H U a trace hend j x.1 hx
  have hprof : historyProfile H (trace j) R.collector.state.toMMap
      (replayLetter H U a trace hend K R alpha) = some e :=
    (congrFun (replayLetter_profile H U a trace hend K R alpha) j).trans halpha
  have hreal := (historyProfile_eq_some_iff H (trace j) R.collector.state.toMMap
    (replayLetter H U a trace hend K R alpha) e).1 hprof
  have hrow := review_rowExtension_succ H U J
    (R.collector.state.level_apply H U a R.collector.index hq) (hreal x hx)
  have hhead : S.succ (h.representative H qx) (e.code H x hx).params
      (e.code H x hx).char = some (theta.representative H x.1) := by
    rw [hraw x hx]
    exact review_head_raw_fan_edge H U a trace hend K R j e x hx
  rw [TraceHistoryState.headRow_representative_eq_rowExtension H U a R.collector.index
    R.collector.state qx (Nat.le_of_eq hq)] at hhead
  have heq := Option.some.inj (hhead.symm.trans hrow)
  exact heq.trans (step_state_apply H U a trace hend K R alpha qx).symm

end ProfileReplayState
end SuccessorTree.SMTree.FatTree
