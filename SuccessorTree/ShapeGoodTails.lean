import SuccessorTree.ShapeFusionExcess
import SuccessorTree.HalesJewett.Forcing
import Mathlib.Tactic

/-!
# Good tails and the Milliken level-refinement algebra

For a one-moving head g at cut c, a tail q at the next cut is good for a set
A when every local identity/letter member of the algebraic line determined by
(g,q) lies in A.

The two elementary identities below are the shape-preserving analogue of the
usual "shift leaves the prefix fixed" identities in Milliken/Hales--Jewett
fusion.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Tails making the whole local line through g land in A. -/
def shapeGoodTails
    (H : SMTree S) {c : Nat}
    (g : AM H c 1)
    (A : Set (AM H c 1)) :
    Set (AM H (g.nextCut H) 1) :=
  {q | ∀ p : LineInput (OneLevelLetter H c),
      H.shapeLineApply g q p ∈ A}

/-- The next cut is strictly above the frozen cut. -/
theorem AM.lt_nextCut
    (H : SMTree S) {c : Nat} (g : AM H c 1) :
    c < g.nextCut H := by
  unfold AM.nextCut
  have hge : c ≤ g.topLevel H := by
    have h := H.levelMap_id_le (g.representative H).map c
    simpa [AM.topLevel] using h
  omega

/-- A tail subspace based at the next cut leaves the head itself unchanged. -/
theorem shapeAct_weaken_nextCut_head
    (H : SMTree S) {c : Nat}
    (g : AM H c 1)
    (U : ShapeSubspace H (g.nextCut H)) :
    H.shapeAct c
        (ShapeSubspace.weaken H (Nat.le_of_lt (g.lt_nextCut H)) U) g = g := by
  exact H.shapeAct_weaken_eq_self_of_top_lt
    (Nat.le_of_lt (g.lt_nextCut H)) U g (Nat.lt_succ_self _)

/-- Refining beyond the next cut acts only on the tail coordinate of the
algebraic line. -/
theorem shapeAct_weaken_shapeLineApply
    (H : SMTree S) {c : Nat}
    (g : AM H c 1)
    (U : ShapeSubspace H (g.nextCut H))
    (q : AM H (g.nextCut H) 1)
    (p : LineInput (OneLevelLetter H c)) :
    H.shapeAct c
        (ShapeSubspace.weaken H (Nat.le_of_lt (g.lt_nextCut H)) U)
        (H.shapeLineApply g q p) =
      H.shapeLineApply g
        (H.shapeAct (g.nextCut H) U q) p := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let P : MMap H := localInputMMap H c p
  let z : T := g.canonical H (P x.1)
  have hPlev : LevelTree.lev (P x.1) ≤ c + 1 := by
    cases p with
    | base =>
        change LevelTree.lev x.1 ≤ c + 1
        omega
    | letter e =>
        rw [e.level_apply H]
        split <;> omega
  have hz :
      LevelTree.lev z ≤ g.nextCut H := by
    calc
      LevelTree.lev z =
          H.levelMap (g.canonical H).map (LevelTree.lev (P x.1)) :=
        (H.levelMap_eq (g.canonical H).map (a := P x.1)).symm
      _ ≤ H.levelMap (g.canonical H).map (c + 1) :=
        (H.levelMap_strictMono (g.canonical H).map).monotone hPlev
      _ = g.nextCut H := g.canonical_level_next H
  have hqrep :
      (H.shapeAct (g.nextCut H) U q).representative H z =
        U.1 (q.representative H z) :=
    H.shapeAct_representative_agrees
      (g.nextCut H) U q z hz
  change
    U.1 (q.representative H (g.canonical H (P x.1))) =
      (H.shapeAct (g.nextCut H) U q).representative H
        (g.canonical H (P x.1))
  exact hqrep.symm

/-- Avoidance of a good-tail set is inherited by further right refinement. -/
theorem shapeGoodTails_avoid_mono
    (H : SMTree S) {c : Nat}
    (g : AM H c 1)
    (A : Set (AM H c 1))
    (U V : ShapeSubspace H (g.nextCut H))
    (hU : (H.shapeSubspaceAction (g.nextCut H)).Avoids U
      (H.shapeGoodTails g A)) :
    (H.shapeSubspaceAction (g.nextCut H)).Avoids
      (ShapeSubspace.comp H U V)
      (H.shapeGoodTails g A) := by
  intro q hq
  apply hU (H.shapeAct (g.nextCut H) V q)
  simpa [shapeSubspaceAction,
    H.shapeAct_comp (g.nextCut H) U V q] using hq

end SMTree
end SuccessorTree
