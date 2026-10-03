import SuccessorTree.ShapeMillikenFusion
import SuccessorTree.ShapeBlockLine
import Mathlib.Tactic

/-!
# Genuine local shape lines in large sets

This closes the only input assumed by ShapeMillikenFusion.  The maximal-
avoider argument already gives a replay line in a large set.  Maximality
forces its common bounded input to end on the last available source level.
Composing that exact input with the canonical finite prefix turns the high
replay line into an exact replay line.  ShapeDirectLine transports it back to
the frozen source cut, and ShapeTwoBlock factors the resulting two-level block
as a head with one good tail.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

theorem replayApplyAM_representative_agrees
    (H : SMTree S) (m : Nat)
    (R : ReplayBlock H m)
    (x : LineInput (OneLevelLetter H m))
    (a : T) (ha : LevelTree.lev a ≤ m) :
    (replayApplyAM H m R x).representative H a =
      R.toMMap (localInputMMap H m x a) := by
  cases x with
  | base =>
      change
        (R.toMMap.toAM H m 1 R.fixesBelow).representative H a =
          R.toMMap a
      exact MMap.toAM_one_representative_agrees
        H R.toMMap m R.fixesBelow a ha
  | letter e =>
      change
        ((MMap.comp H R.toMMap e.toMMap).toAM H m 1 _).representative H a =
          R.toMMap (e.toMMap a)
      exact MMap.toAM_one_representative_agrees
        H (MMap.comp H R.toMMap e.toMMap) m
          (MMap.comp_fixesBelow H R.toMMap e.toMMap m
            R.fixesBelow
            (by
              intro z hz
              exact e.eq_id_below H hz))
          a ha

/-- In the maximal-avoider replay witness the common bounded input must use
the last source level of the old block. -/
theorem maximalReplay_input_top
    (H : SMTree S)
    {n k : Nat}
    (A : Set (AM H n 1))
    (h : AM H n (k + 1))
    (havoid : BlockAvoids H A h)
    (R : ReplayBlock H (h.blockTopLevel H + 1))
    (g : AMBelow H n (n + k + 2))
    (hline :
      ∀ x : LineInput (OneLevelLetter H (h.blockTopLevel H + 1)),
        H.blockEval (H.blockReplayExtension h R x) g.1 ∈ A) :
    g.1.topLevel H = n + k + 1 := by
  have hupper : g.1.topLevel H < n + k + 2 := g.2
  by_contra hne
  have hlt : g.1.topLevel H < n + k + 1 := by omega
  let g0 : AMBelow H n (n + k + 1) := ⟨g.1, hlt⟩
  have hnot := havoid g0
  let hb : AM H n (k + 2) :=
    H.blockReplayExtension h R LineInput.base
  have hext : BlockExtends H h hb :=
    H.blockReplayExtension_extends h R LineInput.base
  have heq :
      H.blockEval h g.1 = H.blockEval hb g.1 :=
    H.blockEval_eq_of_extends hext g.1 hlt
  apply hnot
  rw [heq]
  exact hline LineInput.base

/-- The maximal replay witness canonically determines an exact one-moving
prefix whose terminal level is precisely the replay level. -/
noncomputable def maximalReplayExactPrefix
    (H : SMTree S)
    {n k : Nat}
    (h : AM H n (k + 1))
    (g : AMBelow H n (n + k + 2))
    (hg : g.1.topLevel H = n + k + 1) :
    AMExact H n (h.blockTopLevel H + 1) := by
  let hd := h.hasDepth_id H
  let C : MMap H := H.prefixCanonical hd
  let G : MMap H := g.1.representative H
  let P : MMap H := MMap.comp H C G
  have hCfix : C.FixesBelow H n := by
    intro x hx
    have hreal := H.prefixCanonical_realizes hd
    have hrealVal := congrArg Subtype.val hreal
    change C.restrictLe H (n + k) = h.1.1 at hrealVal
    let xx : InitialNode T (n + k) :=
      ⟨x, by omega⟩
    have hCx : C x = h.1.1 xx := congrFun hrealVal xx
    have hhtop := h.representative_top H
    have hhval := congrArg Subtype.val hhtop
    change (h.representative H).restrictLe H (n + k) = h.1.1 at hhval
    have hhx : h.representative H x = h.1.1 xx :=
      congrFun hhval xx
    calc
      C x = h.1.1 xx := hCx
      _ = h.representative H x := hhx.symm
      _ = x := h.representative_fixesBelow H x hx
  have hPfix : P.FixesBelow H n := by
    intro x hx
    change C (G x) = x
    rw [g.1.representative_fixesBelow H x hx]
    exact hCfix x hx
  let p0 : AM H n 1 := P.toAM H n 1 hPfix
  refine ⟨p0, ?_⟩
  rw [MMap.toAM_one_topLevel H P n hPfix]
  rw [H.levelMap_comp C G n]
  have hGtop : H.levelMap G.map n = n + k + 1 := by
    simpa [G, AM.topLevel] using hg
  rw [hGtop]
  exact H.prefixCanonical_level_succ hd

/-- The original high replay line is exactly an exact replay line through the
prefix constructed above. -/
theorem maximalReplay_crossEval
    (H : SMTree S)
    {n k : Nat}
    (h : AM H n (k + 1))
    (R : ReplayBlock H (h.blockTopLevel H + 1))
    (g : AMBelow H n (n + k + 2))
    (hg : g.1.topLevel H = n + k + 1)
    (x : LineInput (OneLevelLetter H (h.blockTopLevel H + 1))) :
    H.blockEval (H.blockReplayExtension h R x) g.1 =
      H.crossEval (ShapeSubspace.id H n)
        (H.maximalReplayExactPrefix h g hg)
        (replayApplyAM H (h.blockTopLevel H + 1) R x) := by
  let hd := h.hasDepth_id H
  let C : MMap H := H.prefixCanonical hd
  let G : MMap H := g.1.representative H
  let p := H.maximalReplayExactPrefix h g hg
  let q := replayApplyAM H (h.blockTopLevel H + 1) R x
  apply Subtype.ext
  apply Subtype.ext
  funext z
  have hGlev :
      LevelTree.lev (G z.1) ≤ n + k + 1 := by
    calc
      LevelTree.lev (G z.1) ≤ g.1.topLevel H :=
        g.1.level_le_topLevel H z.1 z.2
      _ = n + k + 1 := hg
  have hblockTop :=
    (H.blockReplayExtension h R x).representative_top H
  have hblockVal := congrArg Subtype.val hblockTop
  change
    ((H.blockReplayExtension h R x).representative H).restrictLe H (n + k + 1) =
      (H.prefixReplayApply hd R x).1 at hblockVal
  have hblockAt :=
    congrFun hblockVal ⟨G z.1, hGlev⟩
  have hblockLiteral :
      (H.blockReplayExtension h R x).representative H (G z.1) =
        R.toMMap
          (localInputMMap H (h.blockTopLevel H + 1) x (C (G z.1))) := by
    exact hblockAt
  have hPfix :
      (MMap.comp H C G).FixesBelow H n := by
    intro a ha
    have hp :=
      (H.maximalReplayExactPrefix h g hg).1.representative_fixesBelow H a ha
    have hrep :=
      MMap.toAM_one_representative_agrees
        H (MMap.comp H C G) n
          (by
            intro y hy
            have hreal := H.prefixCanonical_realizes hd
            have hrealVal := congrArg Subtype.val hreal
            change C.restrictLe H (n + k) = h.1.1 at hrealVal
            let yy : InitialNode T (n + k) := ⟨y, by omega⟩
            have hCy : C y = h.1.1 yy := congrFun hrealVal yy
            have hhtop := h.representative_top H
            have hhval := congrArg Subtype.val hhtop
            change (h.representative H).restrictLe H (n + k) = h.1.1 at hhval
            have hhy : h.representative H y = h.1.1 yy :=
              congrFun hhval yy
            calc
              C (G y) = C y := by rw [g.1.representative_fixesBelow H y hy]
              _ = h.1.1 yy := hCy
              _ = h.representative H y := hhy.symm
              _ = y := h.representative_fixesBelow H y hy)
        a ha
    exact hp
  have hpRep :
      p.1.representative H z.1 = C (G z.1) := by
    exact MMap.toAM_one_representative_agrees
      H (MMap.comp H C G) n hPfix z.1 z.2
  have hpLev :
      LevelTree.lev (p.1.representative H z.1) ≤ h.blockTopLevel H + 1 := by
    exact (p.1.level_le_topLevel H z.1 z.2).trans_eq p.2
  have hqRep :
      q.representative H (p.1.representative H z.1) =
        R.toMMap
          (localInputMMap H (h.blockTopLevel H + 1) x
            (p.1.representative H z.1)) :=
    H.replayApplyAM_representative_agrees
      (h.blockTopLevel H + 1) R x
      (p.1.representative H z.1) hpLev
  change
    (H.blockReplayExtension h R x).representative H (G z.1) =
      q.representative H (p.1.representative H z.1)
  rw [hblockLiteral, hqRep, hpRep]

/-- An exact replay line immediately yields a genuine source-cut shape line. -/
theorem shapeLine_of_exactReplay
    (H : SMTree S)
    {n m : Nat}
    (A : Set (AM H n 1))
    (p : AMExact H n m)
    (R : ReplayBlock H m)
    (hline :
      ∀ x : LineInput (OneLevelLetter H m),
        H.crossEval (ShapeSubspace.id H n) p
          (replayApplyAM H m R x) ∈ A) :
    ∃ g : AM H n 1,
      ∃ q : AM H (g.nextCut H) 1,
        q ∈ H.shapeGoodTails g A := by
  let h2 : AM H n 2 :=
    H.replayTwoBlock (ShapeSubspace.id H n) p R
  have h2line :
      ∀ x : LineInput (OneLevelLetter H n),
        H.blockEval h2 (H.lineInputAM n x) ∈ A := by
    intro x
    obtain ⟨y, hy⟩ :=
      H.blockEval_replayTwoBlock_line
        (ShapeSubspace.id H n) p R x
    rw [hy]
    exact hline y
  refine ⟨H.twoBlockHead h2, H.twoBlockTail h2, ?_⟩
  exact H.twoBlockTail_mem_goodTails A h2 h2line

/-- Every large set of one-moving shape maps contains a genuine local shape
line.  This is the line-existence input required by the exact-front Milliken
fusion. -/
theorem largeSetHasShapeLine
    (H : SMTree S) (n : Nat) :
    H.LargeSetHasShapeLine n := by
  intro A hA
  classical
  by_cases hUniv : A = Set.univ
  · let g : AM H n 1 := AM.id1 H n
    let q : AM H (g.nextCut H) 1 := AM.id1 H (g.nextCut H)
    refine ⟨g, q, ?_⟩
    intro p
    simp [hUniv]
  · have hex : ∃ h0 : AM H n 1, h0 ∉ A := by
      by_contra hn
      apply hUniv
      ext g
      constructor
      · intro _
        exact Set.mem_univ g
      · intro _
        by_contra hg
        exact hn ⟨g, hg⟩
    obtain ⟨h0, hh0⟩ := hex
    obtain ⟨k, h, hav, hmax⟩ :=
      H.exists_maximal_avoidingBlock_of_large A hA h0 hh0
    obtain ⟨R, g, hline⟩ :=
      H.replayLine_of_maximal_avoidingBlock A h hav hmax
    have hg := H.maximalReplay_input_top A h hav R g hline
    let p := H.maximalReplayExactPrefix h g hg
    have hcross :
        ∀ x : LineInput (OneLevelLetter H (h.blockTopLevel H + 1)),
          H.crossEval (ShapeSubspace.id H n) p
            (replayApplyAM H (h.blockTopLevel H + 1) R x) ∈ A := by
      intro x
      rw [← H.maximalReplay_crossEval h R g hg x]
      exact hline x
    exact H.shapeLine_of_exactReplay A p R hcross

end SMTree
end SuccessorTree
