import SuccessorTree.FatTree.A4ReplayHJ

/-!
# Rows represented by fat-tree histories

A trace history starts at one ambient cut and lands exactly on a later ambient
cut.  Hence its total M-map can be restricted to a one-moving approximation,
and indeed to an exact one-moving approximation.  Composing with the current
ambient row is the manuscript block `w_j P`.
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

/-- The finite one-moving row represented by a history state. -/
noncomputable def asRow
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    AM H (U.cut a) 1 :=
  P.toMMap.toAM H (U.cut a) 1 P.fixesBelow

/-- The chosen representative of the history row agrees with the history
M-map throughout the frozen source segment. -/
theorem asRow_representative_agrees
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    (x : T) (hx : LevelTree.lev x ≤ U.cut a) :
    (asRow H U a i P).representative H x = P.toMMap x := by
  exact MMap.toAM_one_representative_agrees
    H P.toMMap (U.cut a) P.fixesBelow x hx

/-- The history row ends exactly at the current ambient cut. -/
theorem asRow_rowEndLevel
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    (asRow H U a i P).rowEndLevel H = U.cut (a + i) := by
  change
    H.levelMap ((asRow H U a i P).representative H).map (U.cut a) =
      U.cut (a + i)
  obtain ⟨x, hx⟩ := H.level_nonempty (U.cut a)
  calc
    H.levelMap ((asRow H U a i P).representative H).map (U.cut a) =
        H.levelMap ((asRow H U a i P).representative H).map (LevelTree.lev x) :=
      congrArg (H.levelMap ((asRow H U a i P).representative H).map) hx.symm
    _ = LevelTree.lev ((asRow H U a i P).representative H x) :=
      H.levelMap_eq ((asRow H U a i P).representative H).map (a := x)
    _ = LevelTree.lev (P.toMMap x) :=
      congrArg LevelTree.lev
        (asRow_representative_agrees H U a i P x (Nat.le_of_eq hx))
    _ = U.cut (a + i) := P.level_apply H U a i hx

/-- A history state is an exact one-moving map from its initial ambient cut
to its current ambient cut. -/
noncomputable def asExact
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    AMExact H (U.cut a) (U.cut (a + i)) :=
  ⟨asRow H U a i P, asRow_rowEndLevel H U a i P⟩

/-- The manuscript's first block `w_i P`: follow the history to the current
cut and then apply the current ambient row. -/
noncomputable def headRow
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    AM H (U.cut a) 1 :=
  H.composeAcross (asExact H U a i P) (U.row (a + i))

/-- On the original source segment, the first block is literally ambient-row
composition after the history state. -/
theorem headRow_representative_agrees
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    (x : T) (hx : LevelTree.lev x ≤ U.cut a) :
    (headRow H U a i P).representative H x =
      (U.row (a + i)).representative H (P.toMMap x) := by
  rw [headRow]
  rw [H.composeAcross_representative_agrees
    (asExact H U a i P) (U.row (a + i)) x hx]
  change
    (U.row (a + i)).representative H
      ((asRow H U a i P).representative H x) =
    (U.row (a + i)).representative H (P.toMMap x)
  rw [asRow_representative_agrees H U a i P x hx]

/-- The same action through the ambient canonical extension. The bound on
P(x) is proved explicitly; an arbitrary representative is not identified
with its canonical extension outside the finite row domain. -/
theorem headRow_representative_eq_rowExtension
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i)
    (x : T) (hx : LevelTree.lev x ≤ U.cut a) :
    (headRow H U a i P).representative H x =
      U.rowExtension H (a + i) (P.toMMap x) := by
  have hPx : LevelTree.lev (P.toMMap x) ≤ U.cut (a + i) := by
    rcases lt_or_eq_of_le hx with hlt | heq
    · rw [P.fixesBelow x hlt]
      exact (Nat.le_of_lt hlt).trans
        ((U.cut_strictMono H).monotone (by omega))
    · exact Nat.le_of_eq (P.level_apply H U a i heq)
  exact (headRow_representative_agrees H U a i P x hx).trans
    (U.rowExtension_agrees H (a + i) (P.toMMap x) hPx).symm

/-- The first block ends at the last image level of the corresponding ambient
row. -/
theorem headRow_rowEndLevel
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    (headRow H U a i P).rowEndLevel H =
      (U.row (a + i)).rowEndLevel H := by
  obtain ⟨x, hx⟩ := H.level_nonempty (U.cut a)
  change
    H.levelMap ((headRow H U a i P).representative H).map (U.cut a) =
      (U.row (a + i)).rowEndLevel H
  calc
    H.levelMap ((headRow H U a i P).representative H).map (U.cut a) =
        H.levelMap ((headRow H U a i P).representative H).map (LevelTree.lev x) :=
      congrArg (H.levelMap ((headRow H U a i P).representative H).map) hx.symm
    _ = LevelTree.lev ((headRow H U a i P).representative H x) :=
      H.levelMap_eq ((headRow H U a i P).representative H).map (a := x)
    _ = LevelTree.lev
        ((U.row (a + i)).representative H (P.toMMap x)) :=
      congrArg LevelTree.lev
        (headRow_representative_agrees H U a i P x (Nat.le_of_eq hx))
    _ = H.levelMap (U.row (a + i)).representative.map
        (LevelTree.lev (P.toMMap x)) :=
      (H.levelMap_eq (U.row (a + i)).representative.map
        (a := P.toMMap x)).symm
    _ = H.levelMap (U.row (a + i)).representative.map
        (U.cut (a + i)) := by
      rw [P.level_apply H U a i hx]
    _ = (U.row (a + i)).rowEndLevel H := rfl

/-- Consequently the cut following the first block is exactly the next
ambient cut. -/
theorem headRow_nextCut
    (U : FatTree H) (a i : Nat)
    (P : TraceHistoryState H U a i) :
    (headRow H U a i P).rowEndLevel H + 1 =
      U.cut (a + i + 1) := by
  rw [headRow_rowEndLevel H U a i P]
  exact U.row_cut (a + i)

end TraceHistoryState
end FatTree
end SMTree
end SuccessorTree
