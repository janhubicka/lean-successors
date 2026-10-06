import SuccessorTree.FatTree.ShapeCorrespondence
import SuccessorTree.FatTree.A4Splice

/-!
# Realising algebraic coordinates inside a fat tree

This is the forward direction needed to derive the finite shape theorem from
fat-tree Ellentuck.  It never pulls a geometric map back through an ambient
shape map.
-/

namespace SuccessorTree
namespace SMTree
namespace FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

private theorem map_comp_list_eq_of_pointwise
    (p : List T) (F G Q : MMap H)
    (h : ∀ x ∈ p, F x = G (Q x)) :
    p.map F = (p.map Q).map G := by
  rw [List.map_map]
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = G (Q x) := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = G (Q y) := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons, Function.comp_apply]
      rw [hx, ih hxs]

/-- One-step replacement from the top-level range condition.

A row based at cut n whose top-level range lies in the m-th relative fat
level and whose terminal cut is the next ambient cut is a genuine one-block
reduction of U. -/
theorem appendRow_stemAt_of_topRange
    (U : FatTree H) (n m : Nat) (hnm : n ≤ m)
    (g : AM H (U.cut n) 1)
    (hend : g.rowEndLevel H + 1 = U.cut (m + 1))
    (hrange :
      ∀ a : T, LevelTree.lev a = U.cut n →
        ∃ x : T,
          x ∈ U.liftTo H n m hnm
            (TreeLevel (T := T) (U.cut n)) ∧
          g.representative H a =
            (U.row m).representative H x) :
    StemAt H
      (FiniteFatTree.appendRow H (U.initialSegment H n) g)
      U (m + 1) := by
  have hcd : U.cut n ≤ U.cut m :=
    (U.cut_strictMono H).monotone hnm
  have hgend :
      g.rowEndLevel H = (U.row m).rowEndLevel H := by
    have hUend := U.row_cut m
    omega
  have hdt : U.cut m ≤ g.topLevel H := by
    change U.cut m ≤ g.rowEndLevel H
    rw [hgend]
    exact H.levelMap_id_le (U.row m).representative.map (U.cut m)

  obtain ⟨q, hqtop, hqle⟩ :=
    H.exists_truncate_oneRow g (U.cut m) hcd hdt

  let G : MMap H :=
    H.canonicalExtension (g.representative H) (U.cut n)
  let Q : MMap H :=
    H.canonicalExtension (q.representative H) (U.cut n)
  let R : MMap H := U.rowExtension H m

  have hlift :
      G '' ImmediateSuccessors (T := T)
          (TreeLevel (T := T) (U.cut n)) ⊆
        U.liftTo H n (m + 1) (by omega)
          (TreeLevel (T := T) (U.cut n)) := by
    intro z hz
    rcases hz with ⟨b, ⟨a, ha, hab⟩, rfl⟩
    have halev : LevelTree.lev a = U.cut n := ha
    have hblev : LevelTree.lev b = U.cut n + 1 := by
      rw [LevelTree.covBy_level_eq hab, halev]

    obtain ⟨x, hxLift, hgax⟩ := hrange a halev
    have hxlev : LevelTree.lev x = U.cut m := by
      exact U.liftTo_subset_level H n m hnm
        (fun _ h => h) hxLift

    have hqalev :
        LevelTree.lev (q.representative H a) = U.cut m := by
      calc
        LevelTree.lev (q.representative H a) =
            H.levelMap (q.representative H).map (LevelTree.lev a) :=
          (H.levelMap_eq (q.representative H).map (a := a)).symm
        _ = q.topLevel H := by
          unfold AM.topLevel
          rw [halev]
        _ = U.cut m := hqtop

    have hqaUpper :
        q.representative H a ≤ (U.row m).representative H x := by
      have h := hqle a halev
      rw [hgax] at h
      exact h

    have hxUpper :
        x ≤ (U.row m).representative H x := by
      exact MMap.le_apply_of_fixesBelow H
        ((U.row m).representative H)
        ((U.row m).representative_fixesBelow H) hxlev

    have hqax : q.representative H a = x := by
      rcases LevelTree.comparable_below hqaUpper hxUpper with h | h
      · exact LevelTree.same_level_of_le h
          (hqalev.trans hxlev.symm)
      · exact (LevelTree.same_level_of_le h
          (hxlev.trans hqalev.symm)).symm

    obtain ⟨p, ch, hs⟩ := S.s3 hab

    have hGlevels :
        H.levelMap G.map (LevelTree.lev b) =
          H.levelMap G.map (LevelTree.lev a) + 1 := by
      dsimp [G]
      simpa [halev, hblev] using
        H.canonicalExtension_level_succ
          (g.representative H) (U.cut n) (U.cut n) le_rfl
    have hQlevels :
        H.levelMap Q.map (LevelTree.lev b) =
          H.levelMap Q.map (LevelTree.lev a) + 1 := by
      dsimp [Q]
      simpa [halev, hblev] using
        H.canonicalExtension_level_succ
          (q.representative H) (U.cut n) (U.cut n) le_rfl

    have hGsucc := H.succ_eq_of_consecutive_levels G.map hs hGlevels
    have hQsucc := H.succ_eq_of_consecutive_levels Q.map hs hQlevels

    have hQa : Q a = x := by
      dsimp [Q]
      rw [H.canonicalExtension_agrees
        (q.representative H) (U.cut n) a (by omega)]
      exact hqax

    have hGa : G a = R (Q a) := by
      dsimp [G, R]
      rw [H.canonicalExtension_agrees
        (g.representative H) (U.cut n) a (by omega)]
      rw [hQa]
      rw [U.rowExtension_agrees H m x (Nat.le_of_eq hxlev)]
      exact hgax

    have hparams :
        p.map G = (p.map Q).map R := by
      apply map_comp_list_eq_of_pointwise H
      intro y hy
      have hylt : LevelTree.lev y < U.cut n := by
        have h := S.parameter_level_lt hs hy
        simpa [halev] using h
      have hGfix : G y = y := by
        dsimp [G]
        rw [H.canonicalExtension_agrees
          (g.representative H) (U.cut n) y (Nat.le_of_lt hylt)]
        exact g.representative_fixesBelow H y hylt
      have hQfix : Q y = y := by
        dsimp [Q]
        rw [H.canonicalExtension_agrees
          (q.representative H) (U.cut n) y (Nat.le_of_lt hylt)]
        exact q.representative_fixesBelow H y hylt
      have hRfix : R y = y := by
        dsimp [R]
        exact U.rowExtension_fixesBelow H m y
          (lt_of_lt_of_le hylt hcd)
      rw [hGfix, hQfix, hRfix]

    have hQcov : x ⋖ Q b := by
      have hcov := S.covBy_of_succ_eq_some hQsucc
      simpa [hQa] using hcov

    have hQblev : LevelTree.lev (Q b) = U.cut m + 1 := by
      rw [LevelTree.covBy_level_eq hQcov, hxlev]

    have hRlevels :
        H.levelMap R.map (LevelTree.lev (Q b)) =
          H.levelMap R.map (LevelTree.lev (Q a)) + 1 := by
      dsimp [R]
      rw [hQa, hxlev, hQblev]
      exact H.canonicalExtension_level_succ
        ((U.row m).representative H) (U.cut m) (U.cut m) le_rfl

    have hRsucc :=
      H.succ_eq_of_consecutive_levels R.map hQsucc hRlevels

    have hGb : G b = R (Q b) := by
      apply Option.some.inj
      calc
        some (G b) = S.succ (G a) (p.map G) ch := hGsucc.symm
        _ = S.succ (R (Q a)) ((p.map Q).map R) ch := by
          rw [hGa, hparams]
        _ = some (R (Q b)) := hRsucc

    have hOne :
        R (Q b) ∈
          U.oneLift H m
            (U.liftTo H n m hnm
              (TreeLevel (T := T) (U.cut n))) := by
      refine ⟨Q b, ?_, rfl⟩
      exact ⟨x, hxLift, hQcov⟩

    rw [hGb]
    have hsplit :=
      U.liftTo_split H n m (m + 1) hnm (by omega)
        (TreeLevel (T := T) (U.cut n))
    rw [hsplit, U.liftTo_succ H]
    exact hOne

  exact appendRow_stemAt_of_oneLift H U n (m + 1)
    (by omega) g hend hlift

/-- Every algebraic one-row coordinate of the tail map gives a genuine
one-block fat-tree reduction. -/
theorem tailCoordinateRow_occurs
    (U : FatTree H) (n k : Nat)
    (r : AM H (U.cut n) 1)
    (hr : r.topLevel H = U.cut n + k) :
    StemAt H
      (FiniteFatTree.appendRow H (U.initialSegment H n)
        (tailCoordinateRow H U n r))
      U (n + k + 1) := by
  apply appendRow_stemAt_of_topRange H U n (n + k) (by omega)
    (tailCoordinateRow H U n r)
    (tailCoordinateRow_end H U n k r hr)
  intro a ha
  obtain ⟨y, hy, hval⟩ :=
    tailCoordinateRow_range H U n k r hr a ha
  refine ⟨y, ?_, hval⟩
  unfold FatTree.liftTo
  have hdiff : n + k - n = k := by omega
  simpa [hdiff] using hy

end FatTree
end SMTree
end SuccessorTree
