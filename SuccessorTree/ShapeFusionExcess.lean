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
noncomputable def AM.nextCut
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
          have hge' : c ≤ g.topLevel H := by
            simpa [AM.topLevel] using hge
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

noncomputable def AM.excess
    (H : SMTree S) {c : Nat}
    (r : AM H c 1) : Nat :=
  r.topLevel H - c

theorem firstMoveSplit_tail_excess
    (H : SMTree S) {c : Nat}
    (r : AM H c 1)
    (hmove : c < r.topLevel H) :
    H.levelMap (H.firstMoveSplit r hmove).tail.map (c + 1) - (c + 1) =
      AM.excess H r - 1 := by
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
      _ ≤ g.nextCut H := Nat.le_of_lt (Nat.lt_succ_self _)
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
noncomputable def shapeFusionEval
    (H : SMTree S) {n : Nat}
    (D : ShapeFusionData H n)
    (i : Nat)
    (r : AM H (D.cut i) 1) :
    AM H (D.cut i) 1 :=
  H.shapeAct (D.cut i) (D.tail i) r

/-- The base (zero-excess) coordinate evaluates to the chosen head. -/
theorem shapeFusionEval_id_eq_head
    (H : SMTree S) {n : Nat}
    (D : ShapeFusionData H n) (i : Nat) :
    H.shapeFusionEval D i (AM.id1 H (D.cut i)) = D.head i := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hidTop := (AM.id1 H (D.cut i)).representative_top H
  have hidVal := congrArg Subtype.val hidTop
  change
    ((AM.id1 H (D.cut i)).representative H).restrictLe H (D.cut i) =
      (MMap.id H).restrictLe H (D.cut i) at hidVal
  have hxId0 := congrFun hidVal x
  have hxId :
      (AM.id1 H (D.cut i)).representative H x.1 = x.1 := by
    change
      (AM.id1 H (D.cut i)).representative H x.1 =
        (MMap.id H) x.1 at hxId0
    simpa using hxId0
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


/-- Transport an AM type along equality of its frozen cut. -/
def amCastCut
    (H : SMTree S) {c d : Nat}
    (h : c = d) (a : AM H c 1) : AM H d 1 := by
  subst d
  exact a

@[simp] theorem amCastCut_rfl
    (H : SMTree S) {c : Nat}
    (a : AM H c 1) :
    H.amCastCut rfl a = a := rfl

theorem amCastCut_representative
    (H : SMTree S) {c d : Nat}
    (h : c = d) (a : AM H c 1) :
    (H.amCastCut h a).representative H = a.representative H := by
  subst d
  rfl

theorem amCastCut_topLevel
    (H : SMTree S) {c d : Nat}
    (h : c = d) (a : AM H c 1) :
    (H.amCastCut h a).topLevel H = a.topLevel H := by
  subst d
  rfl

/-- The line-closure field in a form using the explicit cut cast. -/
theorem shapeFusionLine_closed_cast
    (H : SMTree S) {n : Nat}
    (D : ShapeFusionData H n)
    (i : Nat)
    (q : AM H (D.cut (i + 1)) 1)
    (hq : q ∈ D.cell (i + 1))
    (p : LineInput (OneLevelLetter H (D.cut i))) :
    H.shapeLineApply (D.head i)
        (H.amCastCut (D.cut_succ i) q) p ∈ D.cell i := by
  simpa [amCastCut] using D.line_closed i q hq p



/-- One recursive excess step: split the first move of the explicit right
coordinate, transport the remaining tail across the current canonical head,
and obtain an algebraic line over a coordinate at the next cut. -/
theorem shapeFusionExists_eval_step
    (H : SMTree S) {n : Nat}
    (D : ShapeFusionData H n)
    (i : Nat)
    (r : AM H (D.cut i) 1)
    (hmove : D.cut i < r.topLevel H) :
    ∃ q : AM H (D.cut (i + 1)) 1,
      AM.excess H q = AM.excess H r - 1 ∧
      H.shapeFusionEval D i r =
        H.shapeLineApply (D.head i)
          (H.amCastCut (D.cut_succ i) (H.shapeFusionEval D (i + 1) q))
          (.letter (H.firstMoveSplit r hmove).first) := by
  let R := H.firstMoveSplit r hmove
  obtain ⟨t, htfixHead, htlevHead, htcomm⟩ :=
    H.exists_transport_after_head (D.head i) R.tail R.tail_fixes
  have hcut : D.cut (i + 1) = (D.head i).nextCut H :=
    D.cut_succ i
  have htfix : t.FixesBelow H (D.cut (i + 1)) := by
    rw [hcut]
    exact htfixHead
  have htlev :
      H.levelMap t.map (D.cut (i + 1)) =
        D.cut (i + 1) +
          (H.levelMap R.tail.map (D.cut i + 1) - (D.cut i + 1)) := by
    rw [hcut]
    exact htlevHead
  let q : AM H (D.cut (i + 1)) 1 :=
    t.toAM H (D.cut (i + 1)) 1 htfix
  have hqex : AM.excess H q = AM.excess H r - 1 := by
    unfold AM.excess
    rw [show q.topLevel H = H.levelMap t.map (D.cut (i + 1)) by
      exact MMap.toAM_one_topLevel H t (D.cut (i + 1)) htfix]
    rw [htlev]
    have htail :=
      H.firstMoveSplit_tail_excess r hmove
    change
      (D.cut (i + 1) +
          (H.levelMap R.tail.map (D.cut i + 1) - (D.cut i + 1)) -
        D.cut (i + 1)) =
        r.topLevel H - D.cut i - 1
    rw [Nat.add_sub_cancel_left]
    simpa [AM.excess] using htail
  refine ⟨q, hqex, ?_⟩
  let qe : AM H (D.cut (i + 1)) 1 := H.shapeFusionEval D (i + 1) q
  let qline : AM H ((D.head i).nextCut H) 1 :=
    H.amCastCut hcut qe
  have hqlineRep :
      qline.representative H = qe.representative H := by
    exact amCastCut_representative H hcut qe
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hrTop := r.representative_top H
  have hrVal := congrArg Subtype.val hrTop
  change
    (r.representative H).restrictLe H (D.cut i) = r.1.1 at hrVal
  have hrx := congrFun hrVal x
  have hsplitVal := congrArg Subtype.val R.agrees
  change
    (MMap.comp H R.tail R.first.toMMap).restrictLe H (D.cut i) =
      r.1.1 at hsplitVal
  have hsx := congrFun hsplitVal x
  have hrSplit :
      r.representative H x.1 =
        R.tail (R.first.toMMap x.1) := by
    calc
      r.representative H x.1 = r.1.1 x := hrx
      _ = R.tail (R.first.toMMap x.1) := hsx.symm
  have hdec := congrArg
    (fun F : MMap H => F (r.representative H x.1))
    (D.decompose i)
  have hfirstLev :
      LevelTree.lev (R.first.toMMap x.1) ≤ D.cut i + 1 := by
    rw [R.first.level_apply H]
    split <;> omega
  have hcomm :=
    htcomm (R.first.toMMap x.1) hfirstLev
  let z : T :=
    (D.head i).canonical H (R.first.toMMap x.1)
  have hz :
      LevelTree.lev z ≤ D.cut (i + 1) := by
    calc
      LevelTree.lev z =
          H.levelMap ((D.head i).canonical H).map
            (LevelTree.lev (R.first.toMMap x.1)) :=
        (H.levelMap_eq ((D.head i).canonical H).map
          (a := R.first.toMMap x.1)).symm
      _ ≤ H.levelMap ((D.head i).canonical H).map (D.cut i + 1) :=
        (H.levelMap_strictMono ((D.head i).canonical H).map).monotone
          hfirstLev
      _ = (D.head i).nextCut H :=
        (D.head i).canonical_level_next H
      _ = D.cut (i + 1) := hcut.symm
  have hqe :
      qe.representative H z =
        (D.tail (i + 1)).1 (q.representative H z) := by
    exact H.shapeAct_representative_agrees
      (D.cut (i + 1)) (D.tail (i + 1)) q z hz
  have hqrep :
      q.representative H z = t z := by
    exact MMap.toAM_one_representative_agrees
      H t (D.cut (i + 1)) htfix z hz
  change
    (D.tail i).1 (r.representative H x.1) =
      qline.representative H
        ((D.head i).canonical H (R.first.toMMap x.1))
  calc
    (D.tail i).1 (r.representative H x.1) =
        (D.tail (i + 1)).1
          ((D.head i).canonical H (r.representative H x.1)) := hdec
    _ =
        (D.tail (i + 1)).1
          ((D.head i).canonical H
            (R.tail (R.first.toMMap x.1))) := by rw [hrSplit]
    _ =
        (D.tail (i + 1)).1
          (t ((D.head i).canonical H (R.first.toMMap x.1))) := by
      rw [hcomm]
    _ = qe.representative H z := by
      rw [hqe, hqrep]
    _ = qline.representative H z := by
      rw [hqlineRep]


/-- The excess induction: every explicit right coordinate evaluates into the
chosen large cell at its fusion stage. -/
theorem shapeFusionEval_mem
    (H : SMTree S) {n : Nat}
    (D : ShapeFusionData H n) :
    ∀ i : Nat, ∀ r : AM H (D.cut i) 1,
      H.shapeFusionEval D i r ∈ D.cell i := by
  intro i r
  generalize hk : AM.excess H r = k
  induction k using Nat.strong_induction_on generalizing i r with
  | h k ih =>
      by_cases hk0 : k = 0
      · have hexcess0 : AM.excess H r = 0 := hk.trans hk0
        have hex0 : r.topLevel H - D.cut i = 0 := by
          simpa [AM.excess] using hexcess0
        have htopLe : r.topLevel H ≤ D.cut i :=
          Nat.sub_eq_zero_iff_le.mp hex0
        have rid : r = AM.id1 H (D.cut i) := by
          exact AM.eq_id1_of_topLevel_le H r htopLe
        rw [rid, H.shapeFusionEval_id_eq_head D]
        exact D.head_mem i
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have htopGe : D.cut i ≤ r.topLevel H := by
          have hge := H.levelMap_id_le (r.representative H).map (D.cut i)
          simpa [AM.topLevel] using hge
        have hmove : D.cut i < r.topLevel H := by
          have hexpos : 0 < AM.excess H r := by
            rw [hk]
            exact hkpos
          unfold AM.excess at hexpos
          omega
        obtain ⟨q, hqex, heval⟩ :=
          H.shapeFusionExists_eval_step D i r hmove
        have hqk : AM.excess H q = k - 1 := by
          calc
            AM.excess H q = AM.excess H r - 1 := hqex
            _ = k - 1 := by rw [hk]
        have hqmem :
            H.shapeFusionEval D (i + 1) q ∈ D.cell (i + 1) :=
          ih (k - 1) (by omega) (i + 1) q hqk
        rw [heval]
        exact H.shapeFusionLine_closed_cast D i (H.shapeFusionEval D (i + 1) q) hqmem
          (.letter (H.firstMoveSplit r hmove).first)

end SMTree
end SuccessorTree
