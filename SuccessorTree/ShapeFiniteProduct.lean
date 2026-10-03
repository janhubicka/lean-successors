import SuccessorTree.ShapeLocalPigeonhole
import Mathlib.Tactic

/-!
# Finite-dimensional product induction for shape maps

The one-dimensional theorem and its arbitrary-prefix version are now
available.  This file carries out the standard finite product induction:
settle the last moving source level by ordinary front fusion, replace the
colour of a block by the common colour of its one-step extensions, and apply
the induction hypothesis to the shorter prefix.
-/

namespace SuccessorTree
namespace SMTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Action of a frozen-prefix shape subspace on an arbitrary finite AM block. -/
noncomputable def shapeActK
    (H : SMTree S) (n k : Nat)
    (W : ShapeSubspace H n)
    (a : AM H n k) : AM H n k :=
  (MMap.comp H W.1 (a.representative H)).toAM H n k
    (MMap.comp_fixesBelow H W.1 (a.representative H) n
      W.2 (a.representative_fixesBelow H))

/-- A toAM representative agrees with its defining total map throughout the
represented source segment. -/
theorem MMap.toAM_representative_agrees
    (H : SMTree S) (F : MMap H) (n k : Nat)
    (hfix : F.FixesBelow H n)
    (x : T) (hx : LevelTree.lev x < n + k) :
    (F.toAM H n k hfix).representative H x = F x := by
  cases hnk : n + k with
  | zero =>
      omega
  | succ m =>
      have htop := (F.toAM H n k hfix).representative_top H
      have hval := congrArg Subtype.val htop
      change
        ((F.toAM H n k hfix).representative H).restrictLe H m =
          F.restrictLe H m at hval
      have hxm : LevelTree.lev x ≤ m := by omega
      exact congrFun hval ⟨x, hxm⟩

/-- Chosen representatives of a shape action agree with literal composition
on the whole finite block. -/
theorem shapeActK_representative_agrees
    (H : SMTree S) (n k : Nat)
    (W : ShapeSubspace H n)
    (a : AM H n k)
    (x : T) (hx : LevelTree.lev x < n + k) :
    (H.shapeActK n k W a).representative H x =
      W.1 (a.representative H x) := by
  exact MMap.toAM_representative_agrees H
    (MMap.comp H W.1 (a.representative H)) n k
    (MMap.comp_fixesBelow H W.1 (a.representative H) n
      W.2 (a.representative_fixesBelow H))
    x hx

/-- Truncate a finite AM block by one moving source level. -/
noncomputable def AM.dropLast
    (H : SMTree S) {n k : Nat}
    (a : AM H n (k + 1)) : AM H n k :=
  (a.representative H).toAM H n k
    (a.representative_fixesBelow H)

/-- The truncated representative agrees with the original block on its
shorter source segment. -/
theorem AM.dropLast_representative_agrees
    (H : SMTree S) {n k : Nat}
    (a : AM H n (k + 1))
    (x : T) (hx : LevelTree.lev x < n + k) :
    (a.dropLast H).representative H x =
      a.representative H x := by
  exact MMap.toAM_representative_agrees H
    (a.representative H) n k
    (a.representative_fixesBelow H) x hx

/-- Width zero has a unique finite approximation. -/
theorem AM.zero_eq_id
    (H : SMTree S) (n : Nat)
    (a : AM H n 0) :
    a = (MMap.id H).toAM H n 0 (MMap.id_fixesBelow H n) := by
  apply Subtype.ext
  exact (ramseyApproximationSystem H).isInitial_eq_sameLevel a.2

/-- The generic k-action specializes to the previously used one-dimensional
shape action. -/
theorem shapeActK_one
    (H : SMTree S) (n : Nat)
    (W : ShapeSubspace H n)
    (a : AM H n 1) :
    H.shapeActK n 1 W a = H.shapeAct n W a := by
  apply Subtype.ext
  rfl

