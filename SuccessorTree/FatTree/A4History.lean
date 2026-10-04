import SuccessorTree.FatTree.A4Good
import SuccessorTree.ShapeTransport

/-!
# Finite histories for the all-trace fat-tree A4 argument

A history is kept at the level of total M-maps.  Its source cut is fixed at
the ambient cut `a`; after `i` steps the history maps that cut to ambient
cut `a+i`, and every source-level point lies in the corresponding fat Lift.

One history step first applies a one-level letter at the current cut and then
the canonical extension of the current ambient fat-tree row.  This is the
literal recurrence used in the all-trace successor-fan proof.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A finite history starting at ambient cut `a` and ending after `i`
fat-tree rows. -/
structure TraceHistoryState (U : FatTree H) (a i : Nat) where
  toMMap : MMap H
  fixesBelow :
    toMMap.FixesBelow H (U.cut a)
  topLevel :
    H.levelMap toMMap.map (U.cut a) = U.cut (a + i)
  image_mem_lift :
    ∀ x : T, LevelTree.lev x = U.cut a →
      toMMap x ∈
        U.liftTo H a (a + i) (by omega)
          (TreeLevel (T := T) (U.cut a))

namespace TraceHistoryState

instance (U : FatTree H) (a i : Nat) :
    CoeFun (TraceHistoryState H U a i) (fun _ => T → T) :=
  ⟨fun P => P.toMMap⟩

/-- The empty history. -/
noncomputable def initial (U : FatTree H) (a : Nat) :
    TraceHistoryState H U a 0 where
  toMMap := MMap.id H
  fixesBelow := MMap.id_fixesBelow H (U.cut a)
  topLevel := by
    obtain ⟨x, hx⟩ := H.level_nonempty (U.cut a)
    calc
      H.levelMap (MMap.id H).map (U.cut a) =
          LevelTree.lev (MMap.id H x) := by
        simpa [hx] using H.levelMap_eq (MMap.id H).map (a := x)
      _ = U.cut a := by simp [hx]
      _ = U.cut (a + 0) := by simp
  image_mem_lift := by
    intro x hx
    unfold FatTree.liftTo
    simp [TreeLevel, hx]

/-- The current history endpoint of a source-level point lies on the current
ambient cut. -/
theorem level_apply
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    {x : T} (hx : LevelTree.lev x = U.cut a) :
    LevelTree.lev (P x) = U.cut (a + i) := by
  calc
    LevelTree.lev (P x) =
        H.levelMap P.toMMap.map (LevelTree.lev x) :=
      (H.levelMap_eq P.toMMap.map (a := x)).symm
    _ = H.levelMap P.toMMap.map (U.cut a) := by rw [hx]
    _ = U.cut (a + i) := P.topLevel

/-- Advance one history step: choose successors by `E`, then pass through
the current ambient fat-tree row. -/
noncomputable def step
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    (E : OneLevelLetter H (U.cut (a + i))) :
    TraceHistoryState H U a (i + 1) := by
  let r : Nat := U.cut (a + i)
  let R : MMap H := U.rowExtension H (a + i)
  let Q : MMap H :=
    MMap.comp H R (MMap.comp H E.toMMap P.toMMap)
  have hbase_le : U.cut a ≤ r := by
    dsimp [r]
    exact (U.cut_strictMono H).monotone (by omega)
  have hQfix : Q.FixesBelow H (U.cut a) := by
    intro x hx
    have hxr : LevelTree.lev x < r :=
      lt_of_lt_of_le hx hbase_le
    have hP : P.toMMap x = x := P.fixesBelow x hx
    have hE : E.toMMap x = x := E.eq_id_below H hxr
    have hR : R x = x := by
      exact U.rowExtension_fixesBelow H (a + i) x hxr
    change R (E.toMMap (P.toMMap x)) = x
    rw [hP, hE, hR]
  have hQtop :
      H.levelMap Q.map (U.cut a) = U.cut (a + (i + 1)) := by
    rw [H.levelMap_comp R (MMap.comp H E.toMMap P.toMMap) (U.cut a)]
    rw [H.levelMap_comp E.toMMap P.toMMap (U.cut a)]
    rw [P.topLevel]
    have hEtop :
        H.levelMap E.toMMap.map (U.cut (a + i)) =
          U.cut (a + i) + 1 := by
      rw [H.levelMap_of_skipsOnly E.toMMap.map
        (U.cut (a + i)) E.skips]
      simp
    have hRsucc :
        H.levelMap R.map (U.cut (a + i) + 1) =
          U.cut (a + i + 1) := by
      simpa [R, Nat.add_assoc] using
        U.rowExtension_level_succ H (a + i)
    calc
      H.levelMap R.map
          (H.levelMap E.toMMap.map (U.cut (a + i))) =
          H.levelMap R.map (U.cut (a + i) + 1) := by
            rw [hEtop]
      _ = U.cut (a + i + 1) := hRsucc
      _ = U.cut (a + (i + 1)) := by
        rfl
  refine {
    toMMap := Q
    fixesBelow := hQfix
    topLevel := hQtop
    image_mem_lift := ?_
  }
  intro x hx
  have hPlev : LevelTree.lev (P x) = r := by
    simpa [r] using P.level_apply H U a i hx
  have hsucc : P x ⋖ E.toMMap (P x) :=
    H.letter_covBy E hPlev
  have hcur :
      P x ∈ U.liftTo H a (a + i) (by omega)
        (TreeLevel (T := T) (U.cut a)) :=
    P.image_mem_lift x hx
  have hone :
      R (E.toMMap (P x)) ∈
        U.oneLift H (a + i)
          (U.liftTo H a (a + i) (by omega)
            (TreeLevel (T := T) (U.cut a))) := by
    refine ⟨E.toMMap (P x), ?_, rfl⟩
    exact ⟨P x, hcur, hsucc⟩
  have hsplit :=
    U.liftTo_split H a (a + i) (a + i + 1)
      (by omega) (by omega)
      (TreeLevel (T := T) (U.cut a))
  have hlast :=
    U.liftTo_succ H (a + i)
      (U.liftTo H a (a + i) (by omega)
        (TreeLevel (T := T) (U.cut a)))
  have htarget :
      R (E.toMMap (P x)) ∈
        U.liftTo H a (a + i + 1) (by omega)
          (TreeLevel (T := T) (U.cut a)) := by
    rw [hsplit, hlast]
    exact hone
  change
    R (E.toMMap (P x)) ∈
      U.liftTo H a (a + (i + 1)) (by omega)
        (TreeLevel (T := T) (U.cut a))
  simpa only [Nat.add_assoc] using htarget

@[simp] theorem step_apply
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    (E : OneLevelLetter H (U.cut (a + i)))
    (x : T) :
    (step H U a i P E) x =
      U.rowExtension H (a + i) (E.toMMap (P x)) := by
  simp [step]

/-- A history step moves every base-level history point upward in the
underlying tree. -/
theorem le_step
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    (E : OneLevelLetter H (U.cut (a + i)))
    {x : T} (hx : LevelTree.lev x = U.cut a) :
    P x ≤ (step H U a i P E) x := by
  let r : Nat := U.cut (a + i)
  let R : MMap H := U.rowExtension H (a + i)
  have hPlev : LevelTree.lev (P x) = r := by
    simpa [r] using P.level_apply H U a i hx
  have hPR : P x ≤ R (P x) := by
    exact U.le_rowExtension_at_cut H (a + i) hPlev
  have hRE :
      R (P x) ≤ R (E.toMMap (P x)) := by
    exact R.map.map_le_of_le (H.letter_covBy E hPlev).le
  simpa [step_apply] using hPR.trans hRE

end TraceHistoryState

end FatTree
end SMTree
end SuccessorTree
