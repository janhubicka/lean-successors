import SuccessorTree.ShapeAction
import SuccessorTree.ShapeSplit
import SuccessorTree.ShapeTransportAlphabet
import Mathlib.Tactic

/-!
# Exact-level factorisation of one-moving-level shape words

The one-dimensional shape space AM^n_1 carries a finitely branching tree
structure when ordered by terminal target level.  Every word ending at level
m+1 has a predecessor ending at m, followed by a genuine one-level letter at
m.  This is the finite tree used by the Milliken-style fusion proof.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- One-moving-level words ending exactly at target level m. -/
abbrev AMExact
    (H : SMTree S) (n m : Nat) :=
  {g : AM H n 1 // g.topLevel H = m}

noncomputable def amExactToBelow
    (H : SMTree S) (n m : Nat) :
    AMExact H n m → AMBelow H n (m + 1) :=
  fun g => ⟨g.1, by
    rw [g.2]
    omega⟩

theorem amExactToBelow_injective
    (H : SMTree S) (n m : Nat) :
    Function.Injective (H.amExactToBelow n m) := by
  intro g h hgh
  have hv :
      (H.amExactToBelow n m g).1 =
        (H.amExactToBelow n m h).1 :=
    congrArg (fun z : AMBelow H n (m + 1) => z.1) hgh
  exact Subtype.ext hv

noncomputable instance amExactFintype
    (H : SMTree S) (n m : Nat) :
    Fintype (AMExact H n m) := by
  exact Fintype.ofInjective
    (H.amExactToBelow n m)
    (H.amExactToBelow_injective n m)

/-- At the first possible terminal level there is only the identity word. -/
theorem AMExact.eq_id
    (H : SMTree S) {n : Nat}
    (g : AMExact H n n) :
    g.1 = AM.id1 H n := by
  apply AM.eq_id1_of_topLevel_le H g.1
  rw [g.2]

/-- Data supplied by one predecessor step.  We retain total representatives
so later fusion arguments never need to invert an arbitrary shape map. -/
structure ExactPredecessor
    (H : SMTree S) (n m : Nat)
    (g : AMExact H n (m + 1)) where
  pred : MMap H
  pred_fixes : pred.FixesBelow H n
  pred_top : H.levelMap pred.map n = m
  letter : OneLevelLetter H m
  agrees :
    ramseyApprox H (n + 1)
      (MMap.comp H letter.toMMap pred) = g.1.1

/-- Every exact-level word one level above m has an exact-level predecessor at
m followed by one genuine one-level letter at m. -/
noncomputable def exactPredecessor
    (H : SMTree S)
    {n m : Nat} (hnm : n ≤ m)
    (g : AMExact H n (m + 1)) :
    ExactPredecessor H n m g := by
  let K : MMap H := g.1.representative H
  have hKfix : K.FixesBelow H n :=
    g.1.representative_fixesBelow H
  have hKtop : H.levelMap K.map n = m + 1 := by
    exact g.2
  have hcut : SplitCut H K n m := by
    refine ⟨?_, ?_⟩
    · rw [hKtop]
      omega
    · cases n with
      | zero =>
          trivial
      | succ j =>
          have hKj : H.levelMap K.map j = j := by
            apply H.levelMap_eq_of_fixesBelow K (j + 1) hKfix
            omega
          change H.levelMap K.map j < m
          rw [hKj]
          omega
  let hsplit := H.exists_shapeSplit_factor K n m hcut
  let P : MMap H := Classical.choose hsplit
  let hsplitP := Classical.choose_spec hsplit
  let Q : MMap H := Classical.choose hsplitP
  have hsplitSpec := Classical.choose_spec hsplitP
  rcases hsplitSpec with ⟨hPagree, hPtop, hQfix, hQP⟩
  have hPfix : P.FixesBelow H n := by
    intro x hx
    calc
      P x = K x := hPagree x hx
      _ = x := hKfix x hx
  have hQtop : H.levelMap Q.map m = m + 1 := by
    obtain ⟨x, hx⟩ := H.level_nonempty n
    have hPx :
        LevelTree.lev (P x) = m := by
      calc
        LevelTree.lev (P x) =
            H.levelMap P.map n := by
          simpa [hx] using (H.levelMap_eq P.map (a := x)).symm
        _ = m := hPtop
    have hKx :
        LevelTree.lev (K x) = m + 1 := by
      calc
        LevelTree.lev (K x) =
            H.levelMap K.map n := by
          simpa [hx] using (H.levelMap_eq K.map (a := x)).symm
        _ = m + 1 := hKtop
    calc
      H.levelMap Q.map m =
          LevelTree.lev (Q (P x)) := by
        simpa [hPx] using H.levelMap_eq Q.map (a := P x)
      _ = LevelTree.lev (K x) := by
        rw [hQP x (by simpa [hx])]
      _ = m + 1 := hKx
  let e : OneLevelLetter H m :=
    ⟨H.canonicalExtension Q m,
      H.canonicalExtension_skipsOnly_of_oneStep
        Q m hQfix hQtop⟩
  refine {
    pred := P
    pred_fixes := hPfix
    pred_top := hPtop
    letter := e
    agrees := ?_
  }
  have hKapprox := g.1.representative_top H
  apply Subtype.ext
  funext x
  have hPbound :
      LevelTree.lev (P x.1) ≤ m := by
    calc
      LevelTree.lev (P x.1) =
          H.levelMap P.map (LevelTree.lev x.1) :=
        (H.levelMap_eq P.map (a := x.1)).symm
      _ ≤ H.levelMap P.map n :=
        (H.levelMap_strictMono P.map).monotone x.2
      _ = m := hPtop
  change
    H.canonicalExtension Q m (P x.1) = g.1.1.1 x
  rw [H.canonicalExtension_agrees Q m (P x.1) hPbound]
  have hKP : Q (P x.1) = K x.1 :=
    hQP x.1 x.2
  rw [hKP]
  have hval := congrArg Subtype.val hKapprox
  change K.restrictLe H n = g.1.1.1 at hval
  exact congrFun hval x

/-- The predecessor total map itself represents an exact-level word. -/
noncomputable def ExactPredecessor.predWord
    (H : SMTree S)
    {n m : Nat} {g : AMExact H n (m + 1)}
    (D : ExactPredecessor H n m g) :
    AMExact H n m := by
  let p : AM H n 1 := D.pred.toAM H n 1 D.pred_fixes
  refine ⟨p, ?_⟩
  unfold AM.topLevel
  have htop := AM.representative_top H p
  have hval := congrArg Subtype.val htop
  change (p.representative H).restrictLe H n =
    D.pred.restrictLe H n at hval
  obtain ⟨x, hx⟩ := H.level_nonempty n
  have hpoint := congrFun hval ⟨x, by simpa [hx]⟩
  calc
    H.levelMap (p.representative H).map n =
        LevelTree.lev (p.representative H x) := by
      simpa [hx] using H.levelMap_eq (p.representative H).map (a := x)
    _ = LevelTree.lev (D.pred x) := by
      simpa [MMap.restrictLe] using congrArg LevelTree.lev hpoint
    _ = H.levelMap D.pred.map n := by
      simpa [hx] using (H.levelMap_eq D.pred.map (a := x)).symm
    _ = m := D.pred_top

end SMTree
end SuccessorTree
