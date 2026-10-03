import SuccessorTree.ShapeTransportAlphabet
import SuccessorTree.ShapeWordFactor
import Mathlib.Tactic

/-!
# Direct excess induction for shape-function fusion

This file contains the final algebraic induction for the Ramsey theorem on
shape-preserving functions.  No fat subtree or range pullback is used.

A fusion datum consists of explicit one-moving heads v_i and explicit tail
subspaces F_i with
  F_i = F_{i+1} o v_i^+.
The line-closure hypothesis says that every tail word in O_{i+1}, composed
with v_i^+ and a local identity/letter input, lies in O_i.

Every right coordinate r is explicit.  M2 splits off its first move; the
transport lemma pushes the remaining tail through v_i^+; hence the excess
drops by one and the induction advances from i to i+1.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Next cut after a one-moving head. -/
def AM.nextCut
    (H : SMTree S) {c : Nat} (g : AM H c 1) : Nat :=
  g.topLevel H + 1

/-- Canonical total extension of a one-moving head. -/
noncomputable def AM.canonical
    (H : SMTree S) {c : Nat} (g : AM H c 1) : MMap H :=
  H.canonicalExtension (g.representative H) c

theorem AM.canonical_level_cut
    (H : SMTree S) {c : Nat} (g : AM H c 1) :
    H.levelMap (g.canonical H).map c = g.topLevel H := by
  rw [AM.canonical, H.canonicalExtension_level_at_prefix]
  rfl

theorem AM.canonical_fixesBelow
    (H : SMTree S) {c : Nat} (g : AM H c 1) :
    (g.canonical H).FixesBelow H c := by
  intro x hx
  rw [AM.canonical]
  rw [H.canonicalExtension_agrees
    (g.representative H) c x (Nat.le_of_lt hx)]
  exact g.representative_fixesBelow H x hx

/-- Algebraic line determined by a head g and a tail coordinate q. -/
noncomputable def shapeLineApply
    (H : SMTree S)
    {c : Nat}
    (g : AM H c 1)
    (q : AM H (g.nextCut H) 1)
    (p : LineInput (OneLevelLetter H c)) :
    AM H c 1 := by
  let P := localInputMMap H c p
  let F :=
    MMap.comp H (q.representative H)
      (MMap.comp H (g.canonical H) P)
  have hfixQ :
      (q.representative H).FixesBelow H (g.nextCut H) :=
    q.representative_fixesBelow H
  have hfixG : (g.canonical H).FixesBelow H c :=
    g.canonical_fixesBelow H
  have hfixP : P.FixesBelow H c :=
    H.localInputMMap_fixesBelow c p
  exact F.toAM H c 1
    (MMap.comp_fixesBelow H (q.representative H)
      (MMap.comp H (g.canonical H) P) c
      (by
        intro x hx
        apply hfixQ
        exact lt_trans hx (by
          unfold AM.nextCut
          have hge := H.levelMap_id_le (g.representative H).map c
          rw [← g.canonical_level_cut H] at hge
          omega))
      (MMap.comp_fixesBelow H (g.canonical H) P c hfixG hfixP))

/-- The base point of the algebraic line is the head. -/
theorem shapeLineApply_base
    (H : SMTree S)
    {c : Nat}
    (g : AM H c 1)
    (q : AM H (g.nextCut H) 1) :
    H.shapeLineApply g q LineInput.base = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hqfix := q.representative_fixesBelow H
  have hGtop := g.representative_top H
  have hGval := congrArg Subtype.val hGtop
  change (g.representative H).restrictLe H c = g.1.1 at hGval
  have hxG := congrFun hGval x
  have hcanonLev :
      LevelTree.lev (g.canonical H x.1) < g.nextCut H := by
    calc
      LevelTree.lev (g.canonical H x.1) =
          H.levelMap (g.canonical H).map (LevelTree.lev x.1) :=
        (H.levelMap_eq (g.canonical H).map (a := x.1)).symm
      _ ≤ H.levelMap (g.canonical H).map c :=
        (H.levelMap_strictMono (g.canonical H).map).monotone x.2
      _ = g.topLevel H := g.canonical_level_cut H
      _ < g.nextCut H := Nat.lt_succ_self _
  change
    q.representative H (g.canonical H x.1) = g.1.1 x
  rw [hqfix (g.canonical H x.1) hcanonLev]
  rw [AM.canonical, H.canonicalExtension_agrees
    (g.representative H) c x.1 x.2]
  exact hxG

/-- First-move M2 decomposition of a nonidentity right coordinate. -/
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
  let e : OneLevelLetter H c :=
    ⟨H.canonicalExtension P c,
      H.canonicalExtension_skipsOnly_of_oneStep
        P c hPfix hPtop⟩
  have hQtop :
      H.levelMap Q.map (c + 1) = r.topLevel H := by
    obtain ⟨x, hx⟩ := H.level_nonempty c
    have hPx : LevelTree.lev (P x) = c + 1 := by
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
  change Q (H.canonicalExtension P c y.1) = r.1.1 y
  rw [H.canonicalExtension_agrees P c y.1 y.2]
  calc
    Q (P y.1) = R y.1 := hQP y.1 y.2
    _ = r.1.1 y := hRy

def AM.excess
    (H : SMTree S) {c : Nat}
    (r : AM H c 1) : Nat :=
  r.topLevel H - c

theorem firstMoveSplit_tail_excess
    (H : SMTree S) {c : Nat}
    (r : AM H c 1)
    (hmove : c < r.topLevel H) :
    H.levelMap (H.firstMoveSplit r hmove).tail.map (c + 1) - (c + 1) =
      r.excess H - 1 := by
  unfold AM.excess
  rw [(H.firstMoveSplit r hmove).tail_top]
  omega

/-- Abstract direct fusion data for the excess induction. -/
structure ShapeFusionData
    (H : SMTree S) (n : Nat) where
  cut : Nat → Nat
  cut_zero : cut 0 = n
  head : ∀ i, AM H (cut i) 1
  cut_succ : ∀ i, cut (i + 1) = (head i).nextCut H
  tail : ∀ i, ShapeSubspace H (cut i)
  decompose :
    ∀ i,
      (tail i).1 =
        MMap.comp H
          (tail (i + 1)).1
          ((head i).canonical H)
  cell : ∀ i, Set (AM H (cut i) 1)
  head_mem : ∀ i, head i ∈ cell i
  line_closed :
    ∀ i (q : AM H (cut (i + 1)) 1),
      q ∈ cell (i + 1) →
      ∀ p : LineInput (OneLevelLetter H (cut i)),
        H.shapeLineApply (head i) (by simpa [cut_succ i] using q) p ∈ cell i

end SMTree
end SuccessorTree
