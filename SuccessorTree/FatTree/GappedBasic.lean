import SuccessorTree.FatTree.Lift
import SuccessorTree.Block.MarkedCuts

/-!
# Fat lines with cuts in the gaps

Experimental layer only. The existing strong SMTree and original FatTree
are untouched. This definition is a model of the intended weak fat
geometry, and uses the existing finite M-map approximation type to certify
an entire line. A separate weak monoid record will later replace SMTree
once the Ramsey proof is settled.

An old row has width one (AM H c 1) with the NEXT cut forced to one
past its final image level. A gap row has width two (AM H c 2):
its first moving source level c has image ell INSIDE the marked interval,
and its next source level c+1 has image at the right-hand cut c'.
This single finite M-map records the whole-frontier one-variable line:
the neutral prefix before ell and all occurrences after ell are realised
coherently by the same map.

No new independent cut sequence is introduced. The visible level ell is
derived from the row, and the existing cut still terminates the block.
This file proves numerical geometry only, not fat reduction or A4.
-/

namespace SuccessorTree
namespace SMTree
namespace FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

variable (H : SMTree S)

/-- The internal distinguished level of a one-variable marked line. -/
noncomputable def AM.internalLevel {n : Nat} (a : AM H n 2) : Nat :=
  H.levelMap (a.representative H).map n

/-- The target level after the WHOLE line (right-hand cut). -/
noncomputable def AM.markedEnd {n : Nat} (a : AM H n 2) : Nat :=
  H.levelMap (a.representative H).map (n + 1)

/-- The same cut data as in the original fat tree, but each row carries
both the internal visible level and the right-hand end of the line. -/
structure GappedFatTree where
  cut : Nat → Nat
  cut_zero : cut 0 = 0
  row : (i : Nat) → AM H (cut i) 2
  row_cut : ∀ i : Nat, AM.markedEnd H (row i) = cut (i + 1)

namespace GappedFatTree

variable {H}

noncomputable def visible (U : GappedFatTree H) (i : Nat) : Nat :=
  AM.internalLevel H (U.row i)

theorem cut_le_visible (U : GappedFatTree H) (i : Nat) :
    U.cut i ≤ U.visible i := by
  unfold visible AM.internalLevel
  exact H.levelMap_id_le ((U.row i).representative H).map (U.cut i)

theorem visible_lt_next_cut (U : GappedFatTree H) (i : Nat) :
    U.visible i < U.cut (i + 1) := by
  unfold visible AM.internalLevel
  rw [← U.row_cut]
  unfold AM.markedEnd
  exact H.levelMap_strictMono ((U.row i).representative H).map
    (Nat.lt_succ_self (U.cut i))

theorem cut_lt_succ (U : GappedFatTree H) (i : Nat) :
    U.cut i < U.cut (i + 1) :=
  lt_of_le_of_lt (U.cut_le_visible i) (U.visible_lt_next_cut i)

theorem visible_strictMono (U : GappedFatTree H) :
    StrictMono U.visible := by
  apply strictMono_nat_of_lt_succ
  intro i
  exact lt_of_lt_of_le (U.visible_lt_next_cut i) (U.cut_le_visible (i+1))

theorem cut_strictMono (U : GappedFatTree H) :
    StrictMono U.cut := by
  apply strictMono_nat_of_lt_succ
  intro i
  exact U.cut_lt_succ i

/-- Forget the certified rows and retain their two-dimensional schedule.
This reuses the SAME cuts and derives all distinguished levels from rows. -/
noncomputable def toMarkedLevelSchedule (U : GappedFatTree H) :
    SuccessorTree.Block.MarkedLevelSchedule where
  level := U.visible
  cut := U.cut
  level_strict := U.visible_strictMono
  cut_strict := U.cut_strictMono
  cut_zero := U.cut_zero
  inside := fun i => ⟨U.cut_le_visible i, U.visible_lt_next_cut i⟩

/-- A whole-line canonical extension: complete through source level c_i+1,
not merely c_i. Thus its immediate successor image lands ON the next cut. -/
noncomputable def rowExtension (U : GappedFatTree H) (i : Nat) : MMap H :=
  H.canonicalExtension ((U.row i).representative H) (U.cut i + 1)

theorem rowExtension_right_cut (U : GappedFatTree H) (i : Nat) :
    H.levelMap (U.rowExtension i).map (U.cut i + 1) =
      U.cut (i + 1) := by
  calc
    H.levelMap (U.rowExtension i).map (U.cut i + 1) =
        H.levelMap ((U.row i).representative H).map (U.cut i + 1) :=
      H.canonicalExtension_level_at_prefix _ _
    _ = U.cut (i + 1) := U.row_cut i

theorem rowExtension_fixesBelow (U : GappedFatTree H) (i : Nat) :
    (U.rowExtension i).FixesBelow H (U.cut i) := by
  intro x hx
  calc
    U.rowExtension i x = (U.row i).representative H x :=
      H.canonicalExtension_agrees _ _ x (by omega)
    _ = x := (U.row i).representative_fixesBelow H x hx

/-- The LIFT FORMULA is unchanged; only the completed row has width two. -/
noncomputable def oneLift (U : GappedFatTree H) (i : Nat)
    (X : Set T) : Set T :=
  (U.rowExtension i) '' ImmediateSuccessors (T := T) X

theorem oneLift_subset_right_cut (U : GappedFatTree H) (i : Nat)
    {X : Set T} (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.oneLift i X ⊆ TreeLevel (T := T) (U.cut (i + 1)) := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  have hzlev : LevelTree.lev z = U.cut i + 1 :=
    immediateSuccessors_subset_level hX hz
  change LevelTree.lev (U.rowExtension i z) = U.cut (i + 1)
  calc
    LevelTree.lev (U.rowExtension i z) =
        H.levelMap (U.rowExtension i).map (LevelTree.lev z) :=
      (H.levelMap_eq (U.rowExtension i).map (a := z)).symm
    _ = H.levelMap (U.rowExtension i).map (U.cut i + 1) := by rw [hzlev]
    _ = U.cut (i + 1) := U.rowExtension_right_cut i

end GappedFatTree
end FatTree
end SMTree
end SuccessorTree
