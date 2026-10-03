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


/-- The canonical head hits the next cut on the next source level. -/
theorem AM.canonical_level_next
    (H : SMTree S) {c : Nat} (g : AM H c 1) :
    H.levelMap (g.canonical H).map (c + 1) = g.nextCut H := by
  calc
    H.levelMap (g.canonical H).map (c + 1) =
        H.levelMap (g.canonical H).map c + 1 := by
      exact H.canonicalExtension_level_succ
        (g.representative H) c c le_rfl
    _ = g.topLevel H + 1 := by rw [g.canonical_level_cut H]
    _ = g.nextCut H := rfl

/-- A canonical head remains canonical when the prescribed prefix is extended
by one source level. -/
theorem AM.canonical_recanonical_next
    (H : SMTree S) {c : Nat} (g : AM H c 1) :
    H.canonicalExtension (g.canonical H) (c + 1) =
      g.canonical H := by
  symm
  apply H.canonicalExtension_unique
    (g.canonical H) (g.canonical H) (c + 1)
  · intro x hx
    rfl
  · intro ell hell
    apply H.canonicalExtension_tail_mem_levelRange
      (g.representative H) c ell
    have hnext := g.canonical_level_next H
    calc
      H.levelMap (g.representative H).map c =
          g.topLevel H := rfl
      _ < g.nextCut H := Nat.lt_succ_self _
      _ = H.levelMap (g.canonical H).map (c + 1) := hnext.symm
      _ ≤ ell := hell

/-- Chosen representatives of toAM agree with the total map on the finite
source segment they represent. -/
theorem MMap.toAM_one_representative_agrees
    (H : SMTree S) (F : MMap H) (c : Nat)
    (hfix : F.FixesBelow H c)
    (x : T) (hx : LevelTree.lev x ≤ c) :
    (F.toAM H c 1 hfix).representative H x = F x := by
  let a : AM H c 1 := F.toAM H c 1 hfix
  have htop := a.representative_top H
  have hval := congrArg Subtype.val htop
  change (a.representative H).restrictLe H c = F.restrictLe H c at hval
  exact congrFun hval ⟨x, hx⟩

/-- The terminal level of a one-moving approximation built from a total
M-map is the total map's level at the frozen cut. -/
theorem MMap.toAM_one_topLevel
    (H : SMTree S) (F : MMap H) (c : Nat)
    (hfix : F.FixesBelow H c) :
    (F.toAM H c 1 hfix).topLevel H = H.levelMap F.map c := by
  obtain ⟨x, hx⟩ := H.level_nonempty c
  unfold AM.topLevel
  calc
    H.levelMap ((F.toAM H c 1 hfix).representative H).map c =
        LevelTree.lev ((F.toAM H c 1 hfix).representative H x) := by
      simpa [hx] using
        H.levelMap_eq ((F.toAM H c 1 hfix).representative H).map (a := x)
    _ = LevelTree.lev (F x) := by
      rw [MMap.toAM_one_representative_agrees H F c hfix x (by simpa [hx])]
    _ = H.levelMap F.map c := by
      simpa [hx] using (H.levelMap_eq F.map (a := x)).symm

/-- Transport a split tail across a canonical head. The target cut is exactly
the next cut of the head, and excess is preserved. -/
theorem exists_transport_after_head
    (H : SMTree S)
    {c : Nat}
    (g : AM H c 1)
    (s : MMap H)
    (hs : s.FixesBelow H (c + 1)) :
    ∃ t : MMap H,
      t.FixesBelow H (g.nextCut H) ∧
      H.levelMap t.map (g.nextCut H) =
        g.nextCut H + (H.levelMap s.map (c + 1) - (c + 1)) ∧
      ∀ x : T, LevelTree.lev x ≤ c + 1 →
        g.canonical H (s x) = t (g.canonical H x) := by
  obtain ⟨t, htfix, htlev, htcomm⟩ :=
    H.exists_transport_across_canonical
      (g.canonical H) s (c + 1) hs
  have hnext := g.canonical_level_next H
  have hrecanon := g.canonical_recanonical_next H
  refine ⟨t, ?_, ?_, ?_⟩
  · simpa [hnext] using htfix
  · simpa [hnext] using htlev
  · intro x hx
    have h := htcomm x hx
    rw [hrecanon] at h
    exact h

/-- Direct evaluation of a right coordinate in the tail subspace. -/
noncomputable def ShapeFusionData.eval
    (D : ShapeFusionData H n)
    (i : Nat)
    (r : AM H (D.cut i) 1) :
    AM H (D.cut i) 1 :=
  H.shapeAct (D.cut i) (D.tail i) r

/-- The base (zero-excess) coordinate evaluates to the chosen head. -/
theorem ShapeFusionData.eval_id_eq_head
    (D : ShapeFusionData H n) (i : Nat) :
    D.eval i (AM.id1 H (D.cut i)) = D.head i := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hidTop := (AM.id1 H (D.cut i)).representative_top H
  have hidVal := congrArg Subtype.val hidTop
  change
    ((AM.id1 H (D.cut i)).representative H).restrictLe H (D.cut i) =
      (MMap.id H).restrictLe H (D.cut i) at hidVal
  have hxId := congrFun hidVal x
  have hdec := congrArg
    (fun F : MMap H => F x.1) (D.decompose i)
  have hheadLev :
      LevelTree.lev ((D.head i).canonical H x.1) < D.cut (i + 1) := by
    calc
      LevelTree.lev ((D.head i).canonical H x.1) =
          H.levelMap ((D.head i).canonical H).map
            (LevelTree.lev x.1) :=
        (H.levelMap_eq ((D.head i).canonical H).map (a := x.1)).symm
      _ ≤ H.levelMap ((D.head i).canonical H).map (D.cut i) :=
        (H.levelMap_strictMono ((D.head i).canonical H).map).monotone x.2
      _ = (D.head i).topLevel H := (D.head i).canonical_level_cut H
      _ < (D.head i).nextCut H := Nat.lt_succ_self _
      _ = D.cut (i + 1) := (D.cut_succ i).symm
  have htailFix :
      (D.tail (i + 1)).1 ((D.head i).canonical H x.1) =
        (D.head i).canonical H x.1 :=
    (D.tail (i + 1)).2 _ hheadLev
  have hheadTop := (D.head i).representative_top H
  have hheadVal := congrArg Subtype.val hheadTop
  change
    ((D.head i).representative H).restrictLe H (D.cut i) =
      (D.head i).1.1 at hheadVal
  have hxHead := congrFun hheadVal x
  change
    (D.tail i).1
        ((AM.id1 H (D.cut i)).representative H x.1) =
      (D.head i).1.1 x
  rw [hxId]
  calc
    (D.tail i).1 x.1 =
        (D.tail (i + 1)).1 ((D.head i).canonical H x.1) := hdec
    _ = (D.head i).canonical H x.1 := htailFix
    _ = (D.head i).representative H x.1 := by
      rw [AM.canonical, H.canonicalExtension_agrees
        ((D.head i).representative H) (D.cut i) x.1 x.2]
    _ = (D.head i).1.1 x := hxHead

end SMTree
end SuccessorTree
