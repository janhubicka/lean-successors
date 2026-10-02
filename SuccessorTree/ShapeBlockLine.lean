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
    (hab : (ramseyApproximationSystem H).IsInitial (n := i) (m := j) a b)
    (hbc : (ramseyApproximationSystem H).IsInitial (n := j) (m := k) b c) :
    (ramseyApproximationSystem H).IsInitial (n := i) (m := k) a c := by
  rcases hab with ⟨hij, X, hXa, hXb⟩
  rcases hbc with ⟨hjk, Y, hYb, hYc⟩
  have htop : ramseyApprox H j X = ramseyApprox H j Y :=
    hXb.trans hYb.symm
  have hpref : ramseyApprox H i X = ramseyApprox H i Y := by
    by_cases hijEq : i = j
    · subst j
      exact htop
    · exact (ramseyApproximationSystem H).coherent htop i
        (lt_of_le_of_ne hij hijEq)
  have hYa : ramseyApprox H i Y = a :=
    hpref.symm.trans hXa
  exact ⟨hij.trans hjk, Y, hYa, hYc⟩

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
        have hfin' :
            RamseyLeFin H
              (⟨n + k + 1, h.1⟩ :
                (ramseyApproximationSystem H).FiniteApprox)
              ((ramseyApproximationSystem H).finiteApprox 0 (MMap.id H)) := by
          simpa [ramseyFinitization] using hfin
        have hle := ramseyLeFin_level_le H hfin'
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
          have he' : t + 1 < d + 1 := by simpa [d] using he
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
      (ramseyApproximationSystem H).IsInitial
        (n := n + k + 1) (m := n + k + 2) h.1 b :=
    (ramseyApproximationSystem H).isInitial_oneStep hbStep
  have hprefix :
      (ramseyApproximationSystem H).IsInitial
        (n := n) (m := n + k + 1)
        (ramseyApprox H n (MMap.id H)) h.1 := by
    simpa [Nat.add_assoc] using h.2
  exact ⟨b, isInitial_trans H hprefix hhb⟩

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
  rcases hbStep with ⟨X, hXold, hXnew⟩
  intro y
  have hold := congrArg Subtype.val hXold.2
  have hnew := congrArg Subtype.val hXnew
  change X.restrictLe H (n + k) = h.1.1 at hold
  change X.restrictLe H (n + k + 1) = b.1 at hnew
  calc
    h.1.1 y = X y.1 := (congrFun hold y).symm
    _ = b.1 ⟨y.1, y.2.trans (Nat.le_succ (n + k))⟩ := by
      exact congrFun hnew
        ⟨y.1, y.2.trans (Nat.le_succ (n + k))⟩

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
        (n := n) (m := n + k + 2)
        (ramseyApprox H n (MMap.id H)) b
  · let h' : AM H n (k + 2) := ⟨b, hb⟩
    exact fun g : AMBelow H n (n + k + 2) =>
      decide (H.blockEval h' g.1 ∈ A)
  · exact fun _ : AMBelow H n (n + k + 2) => false

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
  have hexg :
      ∃ g : AMBelow H n (n + k + 2),
        H.blockEval hb g.1 ∈ A := by
    simpa only [BlockAvoids, not_forall, not_not] using hbnot
  obtain ⟨g, hgA⟩ := hexg
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
    ∃ k : Nat, ∃ h : AM H n (k + 1),
      ∃ R : ReplayBlock H (h.blockTopLevel H + 1),
      ∃ g : AMBelow H n (n + k + 2),
        ∀ x : LineInput
            (OneLevelLetter H (h.blockTopLevel H + 1)),
          H.blockEval (H.blockReplayExtension h R x) g.1 ∈ A := by
  classical
  by_cases hA : A = Set.univ
  · let h := AM.id1 H n
    let alpha := OneLevelLetter H (h.blockTopLevel H + 1)
    let L0 : StarLine alpha :=
      ⟨[LineSymbol.parameter], by simp⟩
    let L : StarLine alpha :=
      L0.prepend (fullSupport alpha)
    have hLs : Supports L.star := by
      intro e
      exact support_mem_star_prepend
        (fullSupport alpha) L0 (supports_fullSupport alpha) e
    let R : ReplayBlock H (h.blockTopLevel H + 1) :=
      H.replayBlock L hLs
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
