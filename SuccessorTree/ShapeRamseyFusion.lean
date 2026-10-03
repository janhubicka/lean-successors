import SuccessorTree.ShapeLargeShapeLine
import Mathlib.Tactic

/-!
# The second Milliken fusion: from large good tails to a full subspace

ShapeMillikenFusion is the analogue of forcing Lemma 2: from a large set it
produces a refiner, a head, and a large set of good tails.  This file iterates
that construction, exactly as Proposition 1 in the combinatorial-forcing
proof of Hales--Jewett.

At a large stage X with cut c we choose W,g so that g is in the pullback of
X through W and the good tails after g form the next large stage.  The finite
tail of length r is nested as

  W_0 o W_1 o ... o g_1^+ o g_0^+

with the recursive form W o T_next o g^+.  M1 fuses these finite tails.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

structure ShapeLargeStage (H : SMTree S) where
  cut : Nat
  set : Set (AM H cut 1)
  large : (H.shapeSubspaceAction cut).Large set

structure ShapeLargeChoice
    (H : SMTree S) (X : ShapeLargeStage H) where
  refiner : ShapeSubspace H X.cut
  head : AM H X.cut 1
  head_mem : head ∈ H.shapePullback refiner X.set
  good_large :
    (H.shapeSubspaceAction (head.nextCut H)).Large
      (H.shapeGoodTails head (H.shapePullback refiner X.set))

noncomputable def chooseLargeStage
    (H : SMTree S) (X : ShapeLargeStage H) :
    ShapeLargeChoice H X := by
  obtain ⟨W, g, hg, hgood⟩ :=
    H.exists_large_goodTails (H.largeSetHasShapeLine X.cut)
      X.set X.large
  exact ⟨W, g, hg, hgood⟩

noncomputable def nextLargeStage
    (H : SMTree S) (X : ShapeLargeStage H) :
    ShapeLargeStage H where
  cut := (H.chooseLargeStage X).head.nextCut H
  set :=
    H.shapeGoodTails (H.chooseLargeStage X).head
      (H.shapePullback (H.chooseLargeStage X).refiner X.set)
  large := (H.chooseLargeStage X).good_large

/-- The finite nested tail determined by the first r large stages. -/
noncomputable def largeFiniteTail
    (H : SMTree S) (X : ShapeLargeStage H) : Nat → MMap H
  | 0 => MMap.id H
  | r + 1 =>
      MMap.comp H (H.chooseLargeStage X).refiner.1
        (MMap.comp H
          (H.largeFiniteTail (H.nextLargeStage X) r)
          ((H.chooseLargeStage X).head.canonical H))

theorem largeFiniteTail_fixesBelow
    (H : SMTree S) :
    ∀ (X : ShapeLargeStage H) (r : Nat),
      (H.largeFiniteTail X r).FixesBelow H X.cut := by
  intro X r
  induction r generalizing X with
  | zero =>
      exact MMap.id_fixesBelow H X.cut
  | succ r ih =>
      let C := H.chooseLargeStage X
      let Y := H.nextLargeStage X
      have hnext : X.cut < Y.cut := by
        change X.cut < C.head.nextCut H
        exact C.head.lt_nextCut H
      have hfutureY :
          (H.largeFiniteTail Y r).FixesBelow H Y.cut :=
        ih Y
      have hfutureX :
          (H.largeFiniteTail Y r).FixesBelow H X.cut := by
        intro x hx
        exact hfutureY x (lt_trans hx hnext)
      have hinner :
          (MMap.comp H (H.largeFiniteTail Y r)
            (C.head.canonical H)).FixesBelow H X.cut :=
        MMap.comp_fixesBelow H
          (H.largeFiniteTail Y r) (C.head.canonical H) X.cut
          hfutureX (C.head.canonical_fixesBelow H)
      exact MMap.comp_fixesBelow H
        C.refiner.1
        (MMap.comp H (H.largeFiniteTail Y r) (C.head.canonical H))
        X.cut C.refiner.2 hinner

noncomputable def largeFiniteSubspace
    (H : SMTree S) (X : ShapeLargeStage H) (r : Nat) :
    ShapeSubspace H X.cut :=
  ⟨H.largeFiniteTail X r, H.largeFiniteTail_fixesBelow X r⟩

end SMTree
end SuccessorTree
