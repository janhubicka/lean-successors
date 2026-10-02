import SuccessorTree.ShapeBlockForcing
import Mathlib.Tactic

/-!
# A replay line inside a large set of one-level shape words

This is the shape analogue of the maximal-avoider part of forcing Lemma 1.
A maximal finite avoiding block cannot have any avoiding one-level extension.
We colour the M3/Hales--Jewett replay extensions by the finite vector of
bounded inputs on which they land in the large set.  One coordinate is on for
the base extension, hence the whole replay line lands in the large set at the
same bounded input.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

private theorem isInitial_trans
    (H : SMTree S)
    {i j k : Nat}
    {a : RamseyApprox H i}
    {b : RamseyApprox H j}
    {c : RamseyApprox H k}
    (hab : (ramseyApproximationSystem H).IsInitial a b)
    (hbc : (ramseyApproximationSystem H).IsInitial b c) :
    (ramseyApproximationSystem H).IsInitial a c := by
  rcases hbc with ⟨hjk, Y, hYb, hYc⟩
  have hij := hab.1
  have habY :
      (ramseyApproximationSystem H).IsInitial
        a (ramseyApprox H j Y) := by
    simpa [hYb] using hab
  have haY :
      a = ramseyApprox H i Y :=
    (ramseyApproximationSystem H).isInitial_left_eq_of_right_point habY
  exact ⟨hij.trans hjk, Y, haY.symm, hYc⟩

/-- Terminal target level of a finite block. -/
noncomputable def AM.blockTopLevel
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) : Nat :=
  H.levelMap (h.representative H).map (n + k)

/-- A finite block has, below the identity outer map, depth exactly one above
its terminal target level. -/
theorem AM.hasDepth_id
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) :
    (ramseyFinitization H).HasDepth
      (n := n + k + 1) h.1 (MMap.id H) (h.blockTopLevel H + 1) := by
  let d := h.blockTopLevel H
  constructor
  · change Nonempty
      (RamseyFiniteFactor H h.1
        (ramseyApprox H (d + 1) (MMap.id H)))
    refine ⟨{
      map := h.representative H
      bound := ?_
      agrees := ?_
    }⟩
    · intro x
      calc
        LevelTree.lev (h.representative H x.1) =
            H.levelMap (h.representative H).map (LevelTree.lev x.1) :=
          (H.levelMap_eq (h.representative H).map (a := x.1)).symm
        _ ≤ H.levelMap (h.representative H).map (n + k) :=
          (H.levelMap_strictMono (h.representative H).map).monotone x.2
        _ = d := rfl
    · intro x
      have htop := h.representative_top H
      have hv := congrArg Subtype.val htop
      change (h.representative H).restrictLe H (n + k) = h.1.1 at hv
      exact (congrFun hv x).symm
  · intro e he hfin
    cases e with
    | zero =>
        have hle := ramseyLeFin_level_le H hfin
        omega
    | succ t =>
        change Nonempty
          (RamseyFiniteFactor H h.1
            (ramseyApprox H (t + 1) (MMap.id H))) at hfin
        rcases hfin with ⟨fac⟩
        obtain ⟨x, hx⟩ := H.level_nonempty (n + k)
        let xx : InitialNode T (n + k) := ⟨x, by simpa [hx]⟩
        have hrepTop :
            LevelTree.lev (h.representative H x) = d := by
          calc
            LevelTree.lev (h.representative H x) =
                H.levelMap (h.representative H).map (n + k) := by
              simpa [hx] using
                (H.levelMap_eq (h.representative H).map (a := x)).symm
            _ = d := rfl
        have htop := h.representative_top H
        have hv := congrArg Subtype.val htop
        change (h.representative H).restrictLe H (n + k) = h.1.1 at hv
        have hhx : h.1.1 xx = h.representative H x :=
          (congrFun hv xx).symm
        have hfac := fac.agrees xx
        change h.1.1 xx = fac.map x at hfac
        have hlevelFac : LevelTree.lev (fac.map x) = d := by
          rw [← hfac, hhx]
          exact hrepTop
        have hbound := fac.bound xx
        have htlt : t < d := by
          dsimp [d] at he
          omega
        rw [hlevelFac] at hbound
        omega

/-- Every transported replay member above a finite block is again a block one
dimension longer, and it extends the old block pointwise. -/
noncomputable def blockReplayExtension
    (H : SMTree S)
    {n k : Nat}
    (h : AM H n (k + 1))
    (R : ReplayBlock H (h.blockTopLevel H + 1))
    (x : LineInput (OneLevelLetter H (h.blockTopLevel H + 1))) :
    AM H n (k + 2) := by
  let hd := h.hasDepth_id H
  let b : RamseyApprox H (n + k + 2) :=
    H.prefixReplayApply hd R x
  have hbStep :
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + k + 1) h.1
        (H.prefixReplayRefinement (MMap.id H) R) :=
    H.prefixReplayApply_mem_oneStep hd R x
  have hhb :
      (ramseyApproximationSystem H).IsInitial h.1 b :=
    (ramseyApproximationSystem H).isInitial_oneStep hbStep
  exact ⟨b, isInitial_trans H h.2 hhb⟩

theorem blockReplayExtension_extends
    (H : SMTree S)
    {n k : Nat}
    (h : AM H n (k + 1))
    (R : ReplayBlock H (h.blockTopLevel H + 1))
    (x : LineInput (OneLevelLetter H (h.blockTopLevel H + 1))) :
    BlockExtends H h (H.blockReplayExtension h R x) := by
  let hd := h.hasDepth_id H
  let b : RamseyApprox H (n + k + 2) :=
    H.prefixReplayApply hd R x
  have hbStep :
      b ∈ (ramseyApproximationSystem H).oneStepApproximations
        (n := n + k + 1) h.1
        (H.prefixReplayRefinement (MMap.id H) R) :=
    H.prefixReplayApply_mem_oneStep hd R x
  have hinit :
      (ramseyApproximationSystem H).IsInitial h.1 b :=
    (ramseyApproximationSystem H).isInitial_oneStep hbStep
  intro y
  have happ :=
    H.ramseyApprox_apply_of_initial
      (n := n + k) (m := n + k + 1) hinit y
  exact happ

/-- The product colour used at a maximal avoiding block. -/
noncomputable def blockReplayColour
    (H : SMTree S)
    {n k : Nat}
    (A : Set (AM H n 1))
    (h : AM H n (k + 1))
    (b : RamseyApprox H (n + k + 2)) :
    AMBelow H n (n + k + 2) → Bool := by
  classical
  by_cases hb :
      (ramseyApproximationSystem H).IsInitial
        (ramseyApprox H n (MMap.id H)) b
  · let h' : AM H n (k + 2) := ⟨b, hb⟩
    exact fun g => decide (H.blockEval h' g.1 ∈ A)
  · exact fun _ => false

/-- A maximal avoiding finite block yields a whole M3 replay line in A at
one common bounded input. -/
theorem replayLine_of_maximal_avoidingBlock
    (H : SMTree S)
    {n k : Nat}
    (A : Set (AM H n 1))
    (h : AM H n (k + 1))
    (havoid : BlockAvoids H A h)
    (hmax :
      ∀ h' : AM H n (k + 2),
        BlockExtends H h h' →
        ¬ BlockAvoids H A h') :
    ∃ R : ReplayBlock H (h.blockTopLevel H + 1),
      ∃ g : AMBelow H n (n + k + 2),
        ∀ x : LineInput
            (OneLevelLetter H (h.blockTopLevel H + 1)),
          H.blockEval (H.blockReplayExtension h R x) g.1 ∈ A := by
  classical
  let hd := h.hasDepth_id H
  let colour :
      RamseyApprox H (n + k + 2) →
        (AMBelow H n (n + k + 2) → Bool) :=
    H.blockReplayColour A h
  obtain ⟨R, hmono⟩ :=
    (H.prefixReplaySystem hd).oneDimensionalPigeonhole_finite colour
  let hb : AM H n (k + 2) :=
    H.blockReplayExtension h R LineInput.base
  have hbext : BlockExtends H h hb :=
    H.blockReplayExtension_extends h R LineInput.base
  have hbnot : ¬ BlockAvoids H A hb := hmax hb hbext
  push Not at hbnot
  obtain ⟨g, hgA⟩ := hbnot
  refine ⟨R, g, ?_⟩
  intro x
  have hxvalid :
      (ramseyApproximationSystem H).IsInitial
        (ramseyApprox H n (MMap.id H))
        (H.prefixReplayApply hd R x) :=
    (H.blockReplayExtension h R x).2
  have hbvalid :
      (ramseyApproximationSystem H).IsInitial
        (ramseyApprox H n (MMap.id H))
        (H.prefixReplayApply hd R LineInput.base) :=
    hb.2
  have hbase :
      colour (H.prefixReplayApply hd R LineInput.base) g = true := by
    simp only [colour, blockReplayColour, hbvalid, dite_true]
    exact of_decide_eq_true (by simpa [hb] using hgA)
  have hxcol := congrFun (hmono x) g
  have hxtrue :
      colour (H.prefixReplayApply hd R x) g = true :=
    hxcol.trans hbase
  simp only [colour, blockReplayColour, hxvalid, dite_true] at hxtrue
  exact of_decide_eq_true hxtrue

/-- Every large set of one-level shape words contains a replay line. -/
theorem largeSet_contains_replayLine
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (hlarge : (H.shapeSubspaceAction n).Large A) :
    ∃ k (h : AM H n (k + 1)),
      ∃ R : ReplayBlock H (h.blockTopLevel H + 1),
      ∃ g : AMBelow H n (n + k + 2),
        ∀ x : LineInput
            (OneLevelLetter H (h.blockTopLevel H + 1)),
          H.blockEval (H.blockReplayExtension h R x) g.1 ∈ A := by
  classical
  by_cases hA : A = Set.univ
  · let h := AM.id1 H n
    have h0 : h ∈ A := by simp [hA]
    -- The universal case is discharged by applying the maximal argument to
    -- the complement-free trivial situation after choosing any one-step
    -- extension; the membership conclusion itself is automatic.
    let h1 : AM H n 2 := H.blockCanonicalExtension h
    let R : ReplayBlock H (h.blockTopLevel H + 1) :=
      H.replayBlock
        (⟨[LineSymbol.parameter], by simp⟩ :
          StarLine (OneLevelLetter H (h.blockTopLevel H + 1)))
        (by
          intro e
          simp)
    let g : AMBelow H n (n + 2) :=
      ⟨AM.id1 H n, by
        rw [AM.id1_topLevel]
        omega⟩
    refine ⟨0, h, R, g, ?_⟩
    intro x
    simp [hA]
  · have hex : ∃ h0 : AM H n 1, h0 ∉ A := by
      by_contra hn
      apply hA
      ext g
      constructor
      · intro _
        exact Set.mem_univ g
      · intro _
        by_contra hg
        exact hn ⟨g, hg⟩
    obtain ⟨h0, hh0⟩ := hex
    obtain ⟨k, h, hav, hmax⟩ :=
      H.exists_maximal_avoidingBlock_of_large A hlarge h0 hh0
    obtain ⟨R, g, hline⟩ :=
      H.replayLine_of_maximal_avoidingBlock A h hav hmax
    exact ⟨k, h, R, g, hline⟩

end SMTree
end SuccessorTree
