import SuccessorTree.ShapeFatTail
import Mathlib.Tactic

/-!
# Splitting a one-moving coordinate at its first move

For the direct excess induction, a nonidentity r in AM^c_1 is written

  r = s o p

on the finite source segment, where p is a genuine one-level letter at c and
s fixes below c+1.  The terminal level of s at c+1 is the terminal level of r,
so the excess drops by one.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

structure FirstMoveSplit
    (H : SMTree S) (c : Nat)
    (r : AM H c 1) where
  first : OneLevelLetter H c
  tail : MMap H
  tail_fixes : tail.FixesBelow H (c + 1)
  tail_top : H.levelMap tail.map (c + 1) = r.topLevel H
  agrees :
    ramseyApprox H (c + 1)
      (MMap.comp H tail first.toMMap) = r.1

/-- M2 splits off the first source move of any nonidentity one-moving word. -/
noncomputable def firstMoveSplit
    (H : SMTree S) {c : Nat}
    (r : AM H c 1)
    (hmove : c < r.topLevel H) :
    FirstMoveSplit H c r := by
  let R : MMap H := r.representative H
  have hRfix : R.FixesBelow H c :=
    r.representative_fixesBelow H
  have hRtop : H.levelMap R.map c = r.topLevel H := rfl
  have hcut : SplitCut H R c (c + 1) := by
    refine ⟨?_, ?_⟩
    · rw [hRtop]
      omega
    · cases c with
      | zero => trivial
      | succ j =>
          have hRj :
              H.levelMap R.map j = j :=
            H.levelMap_eq_of_fixesBelow R (j + 1) hRfix
              (Nat.lt_succ_self j)
          change H.levelMap R.map j < j + 2
          rw [hRj]
          omega
  let hsplit := H.exists_shapeSplit_factor R c (c + 1) hcut
  let P : MMap H := Classical.choose hsplit
  let hPdata := Classical.choose_spec hsplit
  let Q : MMap H := Classical.choose hPdata
  have hspec := Classical.choose_spec hPdata
  rcases hspec with ⟨hPagree, hPtop, hQfix, hQP⟩
  have hPfix : P.FixesBelow H c := by
    intro x hx
    calc
      P x = R x := hPagree x hx
      _ = x := hRfix x hx
  have hEtop :
      H.levelMap P.map c = c + 1 := hPtop
  let e : OneLevelLetter H c :=
    ⟨H.canonicalExtension P c,
      H.canonicalExtension_skipsOnly_of_oneStep
        P c hPfix hEtop⟩
  have hQtop :
      H.levelMap Q.map (c + 1) = r.topLevel H := by
    obtain ⟨x, hx⟩ := H.level_nonempty c
    have hPx :
        LevelTree.lev (P x) = c + 1 := by
      calc
        LevelTree.lev (P x) =
            H.levelMap P.map c := by
          simpa [hx] using (H.levelMap_eq P.map (a := x)).symm
        _ = c + 1 := hPtop
    calc
      H.levelMap Q.map (c + 1) =
          LevelTree.lev (Q (P x)) := by
        simpa [hPx] using H.levelMap_eq Q.map (a := P x)
      _ = LevelTree.lev (R x) := by
        rw [hQP x (by simpa [hx])]
      _ = H.levelMap R.map c := by
        simpa [hx] using (H.levelMap_eq R.map (a := x)).symm
      _ = r.topLevel H := hRtop
  refine {
    first := e
    tail := Q
    tail_fixes := hQfix
    tail_top := hQtop
    agrees := ?_
  }
  apply Subtype.ext
  funext y
  have hRfin := r.representative_top H
  have hRval := congrArg Subtype.val hRfin
  change R.restrictLe H c = r.1.1 at hRval
  have hRy := congrFun hRval y
  have hPbound :
      LevelTree.lev (P y.1) ≤ c + 1 := by
    calc
      LevelTree.lev (P y.1) =
          H.levelMap P.map (LevelTree.lev y.1) :=
        (H.levelMap_eq P.map (a := y.1)).symm
      _ ≤ H.levelMap P.map c :=
        (H.levelMap_strictMono P.map).monotone y.2
      _ = c + 1 := hPtop
  change Q (H.canonicalExtension P c y.1) = r.1.1 y
  rw [H.canonicalExtension_agrees P c y.1 y.2]
  calc
    Q (P y.1) = R y.1 := hQP y.1 y.2
    _ = r.1.1 y := hRy

/-- The tail coordinate of a first-move split has exactly one less excess. -/
theorem firstMoveSplit_tail_excess
    (H : SMTree S) {c : Nat}
    (r : AM H c 1)
    (hmove : c < r.topLevel H) :
    H.levelMap (H.firstMoveSplit r hmove).tail.map (c + 1) - (c + 1) =
      r.topLevel H - c - 1 := by
  rw [(H.firstMoveSplit r hmove).tail_top]
  omega

end SMTree
end SuccessorTree
