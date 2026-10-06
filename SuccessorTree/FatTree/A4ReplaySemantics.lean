import SuccessorTree.FatTree.A4ReplayCoherence
import SuccessorTree.FatTree.A4LineTail

/-!
# Actual-edge semantics of fat-tree replay

Replay correctness must also cover bottom profile coordinates. We therefore
use actual recorded successor codes, not equality of optional fan profiles.
The first lemma moves a duplicated recorded edge through an ambient row;
the second identifies the code used by every later replay state.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

private theorem map_eq_self_of_fixed {A : Type*} (f : A → A) (xs : List A)
    (h : ∀ x ∈ xs, f x = x) : xs.map f = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, hx, ih hxs]

/-- Duplicating a recorded edge before an ambient row agrees pointwise with
duplicating it after that row. The old successor parameters are fixed by the
row, and its canonical extension preserves the consecutive pair of levels. -/
theorem rowExtension_duplicate_recorded_edge
    (U : FatTree H) (i : Nat) {r : Nat} (hr : r < U.cut i)
    {a b z : T} (ha : LevelTree.lev a = r)
    (hb : LevelTree.lev b = U.cut i)
    {params : List T} {ch : Label}
    (hedge : S.succ a params ch = some z) (hzb : z ≤ b) :
    U.rowExtension H i (H.duplicate r (U.cut i) hr b) =
      H.duplicate r ((U.row i).rowEndLevel H)
        (hr.trans_le (H.levelMap_id_le (U.row i).representative.map (U.cut i)))
        (U.rowExtension H i b) := by
  let R := U.rowExtension H i
  let ell := (U.row i).rowEndLevel H
  have hrell : r < ell :=
    hr.trans_le (H.levelMap_id_le (U.row i).representative.map (U.cut i))
  have hfirst := H.duplicate_rule r (U.cut i) hr a b params ch z ha hb hedge hzb
  have hdb : LevelTree.lev (H.duplicate r (U.cut i) hr b) = U.cut i + 1 := by
    rw [LevelTree.covBy_level_eq (S.covBy_of_succ_eq_some hfirst), hb]
  have hlevels :
      H.levelMap R.map (LevelTree.lev (H.duplicate r (U.cut i) hr b)) =
        H.levelMap R.map (LevelTree.lev b) + 1 := by
    rw [hdb, hb]
    change H.levelMap (U.rowExtension H i).map (U.cut i + 1) =
      H.levelMap (U.rowExtension H i).map (U.cut i) + 1
    rw [U.rowExtension_level_succ H i, U.rowExtension_level_at_cut H i]
    exact (U.row_cut i).symm
  have hparams : params.map R.map = params := by
    apply map_eq_self_of_fixed
    intro p hp
    apply U.rowExtension_fixesBelow H i
    have hpr := S.parameter_level_lt hedge hp
    rw [ha] at hpr
    exact hpr.trans hr
  have hrow := H.succ_eq_of_consecutive_levels R.map hfirst hlevels
  rw [hparams] at hrow
  have hRb : LevelTree.lev (R b) = ell := by
    calc
      LevelTree.lev (R b) = H.levelMap R.map (LevelTree.lev b) :=
        (H.levelMap_eq R.map (a := b)).symm
      _ = H.levelMap R.map (U.cut i) := by rw [hb]
      _ = ell := U.rowExtension_level_at_cut H i
  have hbR : b ≤ R b := U.le_rowExtension_at_cut H i hb
  have hafter := H.duplicate_rule r ell hrell a (R b) params ch z
    ha hRb hedge (hzb.trans hbR)
  exact Option.some.inj (hrow.symm.trans hafter)

namespace ProfileReplayState

variable {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
variable {U : FatTree H} {a : Nat} {trace : C → AM H c 1}
variable (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
variable {K : ProfileCollector H U a trace}

/-- Every replayed letter uses the actual code of its original occurrence,
including at coordinates whose finite raw-fan profile is bottom. -/
theorem replayLetter_rule_from_original
    (R : ProfileReplayState H U a trace hend K)
    (alpha : SeenProfile H K) (j : C)
    (x : InitialNode T c) (hx : LevelTree.lev x.1 = c)
    (params : List T) (ch : Label)
    (hcode : S.succ
      ((K.occurrence alpha.1 alpha.2).base ((trace j).representative H x.1))
      params ch = some
        ((K.occurrence alpha.1 alpha.2).letter.toMMap
          ((K.occurrence alpha.1 alpha.2).base ((trace j).representative H x.1)))) :
    S.succ (R.collector.state ((trace j).representative H x.1)) params ch =
      some ((replayLetter H U a trace hend K R alpha).toMMap
        (R.collector.state ((trace j).representative H x.1))) := by
  let occ := K.occurrence alpha.1 alpha.2
  let qx := (trace j).representative H x.1
  have hq : LevelTree.lev qx = (trace j).rowEndLevel H := by
    calc
      LevelTree.lev qx =
          H.levelMap ((trace j).representative H).map (LevelTree.lev x.1) :=
        (H.levelMap_eq ((trace j).representative H).map (a := x.1)).symm
      _ = (trace j).rowEndLevel H := by rw [hx]; rfl
  have hbase : LevelTree.lev (occ.base qx) = occ.level := by
    calc
      LevelTree.lev (occ.base qx) = H.levelMap occ.base.map (LevelTree.lev qx) :=
        (H.levelMap_eq occ.base.map (a := qx)).symm
      _ = H.levelMap occ.base.map ((trace j).rowEndLevel H) := by rw [hq]
      _ = occ.level := occ.base_top j
  have hstate : LevelTree.lev (R.collector.state qx) =
      U.cut (a + R.collector.index) :=
    R.collector.state.level_apply H U a R.collector.index (hq.trans (hend j))
  have hbelow := ProfileCollector.original_occurrence_endpoint_below H hend
    R.reachable alpha.1 alpha.2 j x hx
  rw [replayLetter_eq_fixed H hend R alpha]
  exact H.duplicate_rule occ.level (U.cut (a + R.collector.index))
    (fixed_occurrence_level_lt H hend R alpha)
    (occ.base qx) (R.collector.state qx) params ch
    (occ.letter.toMMap (occ.base qx)) hbase hstate hcode hbelow

end ProfileReplayState
end SuccessorTree.SMTree.FatTree
