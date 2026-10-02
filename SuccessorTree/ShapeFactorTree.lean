import SuccessorTree.ShapeTransportAlphabet
import SuccessorTree.ShapeAction
import Mathlib.Tactic

/-!
# The finite-factor tree of one-moving-level shape maps

Every nontrivial member of AM^n_1 can be peeled by M2 at its last target
level. The predecessor ends exactly one target level earlier and the outer
factor is a genuine one-level letter at that predecessor level.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Exact target-level slice of AM^n_1. -/
abbrev AMExact
    (H : SMTree S) (n m : Nat) :=
  {g : AM H n 1 // g.topLevel H = m}

/-- A one-level factor applied after a predecessor word. -/
noncomputable def factorEdgeApply
    (H : SMTree S)
    {n m : Nat}
    (p : AMExact H n m)
    (e : OneLevelLetter H m) :
    AM H n 1 :=
  (MMap.comp H e.toMMap (p.1.representative H)).toAM H n 1
    (MMap.comp_fixesBelow H e.toMMap (p.1.representative H) n
      (by
        intro x hx
        exact e.eq_id_below H
          (lt_trans hx (by
            have hnm : n ≤ m := by
              have hge := H.levelMap_id_le (p.1.representative H).map n
              rw [← p.2] at hge
              exact hge
            exact lt_of_lt_of_le hx hnm)))
      p.1.representative_fixesBelow)

/-- Applying one factor raises the exact terminal level by one. -/
theorem factorEdgeApply_topLevel
    (H : SMTree S)
    {n m : Nat}
    (p : AMExact H n m)
    (e : OneLevelLetter H m) :
    (H.factorEdgeApply p e).topLevel H = m + 1 := by
  unfold factorEdgeApply AM.topLevel
  rw [H.levelMap_comp e.toMMap (p.1.representative H) n]
  rw [p.2]
  rw [H.levelMap_of_skipsOnly e.toMMap.map m e.skips]
  simp

/-- Exact target slices are finite. -/
noncomputable instance amExactFintype
    (H : SMTree S) (n m : Nat) :
    Fintype (AMExact H n m) := by
  classical
  let B : Type u := AMBelow H n (m + 1)
  letI : Fintype B := amBelowFintype H n (m + 1)
  let S' : Finset B :=
    Finset.univ.filter (fun g => g.1.topLevel H = m)
  let e : AMExact H n m ≃ {g : B // g ∈ S'} where
    toFun g := by
      let b : B := ⟨g.1, by rw [g.2]; omega⟩
      refine ⟨b, ?_⟩
      simp [S', b, g.2]
    invFun g := ⟨g.1.1, by
      have hg := g.2
      simp [S'] at hg
      exact hg⟩
    left_inv g := by
      apply Subtype.ext
      rfl
    right_inv g := by
      apply Subtype.ext
      rfl
  exact Fintype.ofEquiv _ e.symm

