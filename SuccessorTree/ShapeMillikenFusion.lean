import SuccessorTree.ShapeTwoBlock
import Mathlib.Tactic

/-!
# Milliken fusion for one-moving shape maps

This file proves the direct fusion lemma needed to upgrade the one-dimensional
pigeonhole theorem to the Ramsey theorem for AM^n_1.

The construction is the usual Milliken fusion.  At terminal level m we process
the finite front AMExact n m.  If a scheduled head has a large good-tail set
we stop.  Otherwise we right-refine at level m+1 by a subspace avoiding those
good tails.  Such a refinement fixes every word ending before m+1, so all
earlier decisions survive.  M1 gives the diagonal limit.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Pull back a set of one-moving words through a shape subspace. -/
def shapePullback
    (H : SMTree S) {n : Nat}
    (W : ShapeSubspace H n)
    (A : Set (AM H n 1)) :
    Set (AM H n 1) :=
  (H.shapeSubspaceAction n).pullback W A

@[simp] theorem mem_shapePullback
    (H : SMTree S) {n : Nat}
    (W : ShapeSubspace H n)
    (A : Set (AM H n 1))
    (g : AM H n 1) :
    g ∈ H.shapePullback W A ↔ H.shapeAct n W g ∈ A :=
  Iff.rfl

/-- No tail completes the local line through g inside the pulled-back set. -/
def ShapeLineBad
    (H : SMTree S) {n : Nat}
    (W : ShapeSubspace H n)
    (A : Set (AM H n 1))
    (g : AM H n 1) : Prop :=
  ∀ q : AM H (g.nextCut H) 1,
    q ∉ H.shapeGoodTails g (H.shapePullback W A)

/-- A scheduled head is settled once it is either absent from the current
pullback or its whole good-tail set has been killed. -/
def ShapeSettled
    (H : SMTree S) {n : Nat}
    (W : ShapeSubspace H n)
    (A : Set (AM H n 1))
    (g : AM H n 1) : Prop :=
  g ∉ H.shapePullback W A ∨ H.ShapeLineBad W A g

/-- Refining at level m leaves every word ending strictly before m unchanged. -/
theorem shapeAct_eq_of_fusionStep_above
    (H : SMTree S) {n m : Nat}
    {W W' : ShapeSubspace H n}
    (hstep : FusionStep H (m - 1) W.1 W'.1)
    (g : AM H n 1)
    (hg : g.topLevel H < m) :
    H.shapeAct n W' g = H.shapeAct n W g := by
  rcases hstep with ⟨K, hK, hWK⟩
  have hnm : n ≤ m := by
    have hge := H.levelMap_id_le (g.representative H).map n
    have htop : n ≤ g.topLevel H := by
      simpa [AM.topLevel] using hge
    omega
  let U : ShapeSubspace H m := ⟨K, by
    intro x hx
    exact hK x (by omega)⟩
  let Uw : ShapeSubspace H n := ShapeSubspace.weaken H hnm U
  have hW' :
      W' = ShapeSubspace.comp H W Uw := by
    apply Subtype.ext
    apply MMap.ext_apply
    intro x
    have hEq := congrArg (fun F : MMap H => F x) hWK
    exact hEq
  rw [hW']
  rw [H.shapeAct_comp n W Uw g]
  exact congrArg (fun z => H.shapeAct n W z)
    (H.shapeAct_weaken_eq_self_of_top_lt hnm U g hg)

/-- A fusion step above the next cut preserves an already killed good-tail
set. -/
theorem shapeLineBad_mono_fusionStep
    (H : SMTree S) {n m : Nat}
    {W W' : ShapeSubspace H n}
    (hstep : FusionStep H (m - 1) W.1 W'.1)
    (A : Set (AM H n 1))
    (g : AM H n 1)
    (hgm : g.nextCut H ≤ m)
    (hbad : H.ShapeLineBad W A g) :
    H.ShapeLineBad W' A g := by
  rcases hstep with ⟨K, hK, hWK⟩
  have hnm : n ≤ m := by
    exact le_trans (Nat.le_of_lt (g.lt_nextCut H)) hgm
  let U : ShapeSubspace H m := ⟨K, by
    intro x hx
    exact hK x (by omega)⟩
  let Ug : ShapeSubspace H (g.nextCut H) :=
    ShapeSubspace.weaken H hgm U
  let Un : ShapeSubspace H n :=
    ShapeSubspace.weaken H hnm U
  have hW' :
      W' = ShapeSubspace.comp H W Un := by
    apply Subtype.ext
    apply MMap.ext_apply
    intro x
    exact congrArg (fun F : MMap H => F x) hWK
  intro q hq
  apply hbad (H.shapeAct (g.nextCut H) Ug q)
  intro p
  have hqLine := hq p
  rw [hW'] at hqLine
  change
    H.shapeAct n W
      (H.shapeAct n Un (H.shapeLineApply g q p)) ∈ A at hqLine
  have hweaken :
      Un =
        ShapeSubspace.weaken H (Nat.le_of_lt (g.lt_nextCut H)) Ug := by
    apply Subtype.ext
    rfl
  rw [hweaken,
    H.shapeAct_weaken_shapeLineApply g Ug q p] at hqLine
  exact hqLine

/-- Being settled is preserved by any later fusion step above the head's next
cut. -/
theorem shapeSettled_mono_fusionStep
    (H : SMTree S) {n m : Nat}
    {W W' : ShapeSubspace H n}
    (hstep : FusionStep H (m - 1) W.1 W'.1)
    (A : Set (AM H n 1))
    (g : AM H n 1)
    (hgm : g.nextCut H ≤ m)
    (hsettled : H.ShapeSettled W A g) :
    H.ShapeSettled W' A g := by
  rcases hsettled with hnot | hbad
  · left
    intro hmem
    apply hnot
    have htop : g.topLevel H < m := by
      unfold AM.nextCut at hgm
      omega
    have heq := H.shapeAct_eq_of_fusionStep_above hstep g htop
    change H.shapeAct n W' g ∈ A at hmem
    change H.shapeAct n W g ∉ A
    simpa [heq] using hmem
  · right
    exact H.shapeLineBad_mono_fusionStep hstep A g hgm hbad

/-- If the current good-tail set is not large, one fusion step kills it. -/
theorem exists_fusionStep_killing_goodTails
    (H : SMTree S) {n : Nat}
    (W : ShapeSubspace H n)
    (A : Set (AM H n 1))
    (g : AM H n 1)
    (hnot :
      ¬ (H.shapeSubspaceAction (g.nextCut H)).Large
        (H.shapeGoodTails g (H.shapePullback W A))) :
    ∃ W' : ShapeSubspace H n,
      FusionStep H (g.nextCut H - 1) W.1 W'.1 ∧
      H.ShapeLineBad W' A g := by
  obtain ⟨U, hU⟩ :=
    ((H.shapeSubspaceAction (g.nextCut H)).not_large_iff_exists_avoids
      (H.shapeGoodTails g (H.shapePullback W A))).mp hnot
  have hng : n ≤ g.nextCut H :=
    Nat.le_of_lt (g.lt_nextCut H)
  let Un : ShapeSubspace H n :=
    ShapeSubspace.weaken H hng U
  let W' : ShapeSubspace H n :=
    ShapeSubspace.comp H W Un
  have hstep :
      FusionStep H (g.nextCut H - 1) W.1 W'.1 := by
    refine ⟨U.1, ?_, ?_⟩
    · intro x hx
      exact U.2 x (by
        have hpos : 0 < g.nextCut H := lt_of_le_of_lt (Nat.zero_le n) (g.lt_nextCut H)
        omega)
    · rfl
  refine ⟨W', hstep, ?_⟩
  intro q hq
  apply hU q
  intro p
  have hline := hq p
  change H.shapeAct n W' (H.shapeLineApply g q p) ∈ A at hline
  change
    H.shapeAct n W
      (H.shapeAct n Un (H.shapeLineApply g q p)) ∈ A at hline
  rw [H.shapeAct_weaken_shapeLineApply g U q p] at hline
  exact hline

/-- Under the contradiction hypothesis that no large good-tail set exists,
every finite exact front can be settled by refinements at its next level. -/
private theorem settleExactFinset
    (H : SMTree S) {n m : Nat}
    (hnm : n ≤ m)
    (A : Set (AM H n 1))
    (hNo :
      ∀ (W : ShapeSubspace H n) (g : AM H n 1),
        g ∈ H.shapePullback W A →
        ¬ (H.shapeSubspaceAction (g.nextCut H)).Large
          (H.shapeGoodTails g (H.shapePullback W A)))
    (P : Finset (AMExact H n m))
    (W : ShapeSubspace H n) :
    ∃ W' : ShapeSubspace H n,
      FusionStep H m W.1 W'.1 ∧
      ∀ p ∈ P, H.ShapeSettled W' A p.1 := by
  classical
  induction P using Finset.induction_on generalizing W with
  | empty =>
      refine ⟨W, ?_, ?_⟩
      · refine ⟨MMap.id H, MMap.id_fixesBelow H (m + 1), ?_⟩
        apply MMap.ext_apply
        intro x
        rfl
      · simp
  | @insert p P hp ih =>
      obtain ⟨W₁, hW₁, hsettled⟩ := ih W
      by_cases hmem : p.1 ∈ H.shapePullback W₁ A
      · have hnot := hNo W₁ p.1 hmem
        obtain ⟨W₂, hW₂raw, hpbad⟩ :=
          H.exists_fusionStep_killing_goodTails W₁ A p.1 hnot
        have hpNext :
            p.1.nextCut H = m + 1 := by
          unfold AM.nextCut
          rw [p.2]
        have hW₂ : FusionStep H m W₁.1 W₂.1 := by
          simpa [hpNext] using hW₂raw
        have hWW₂ : FusionStep H m W.1 W₂.1 := by
          rcases hW₁ with ⟨K₁, hK₁, hEq₁⟩
          rcases hW₂ with ⟨K₂, hK₂, hEq₂⟩
          refine ⟨MMap.comp H K₁ K₂, ?_, ?_⟩
          · exact MMap.comp_fixesBelow H K₁ K₂ (m + 1) hK₁ hK₂
          · rw [hEq₂, hEq₁]
            apply MMap.ext_apply
            intro x
            rfl
        refine ⟨W₂, hWW₂, ?_⟩
        intro q hq
        have hcases : q = p ∨ q ∈ P := by
          simpa [hp] using hq
        rcases hcases with rfl | hqP
        · exact Or.inr hpbad
        · have hqNext :
              q.1.nextCut H ≤ m + 1 := by
            unfold AM.nextCut
            rw [q.2]
          exact H.shapeSettled_mono_fusionStep hW₂ A q.1 hqNext
            (hsettled q hqP)
      · refine ⟨W₁, hW₁, ?_⟩
        intro q hq
        have hcases : q = p ∨ q ∈ P := by
          simpa [hp] using hq
        rcases hcases with rfl | hqP
        · exact Or.inl hmem
        · exact hsettled q hqP

/-- Settle the whole exact target-level front. -/
theorem settleExactFront
    (H : SMTree S) {n m : Nat}
    (hnm : n ≤ m)
    (A : Set (AM H n 1))
    (hNo :
      ∀ (W : ShapeSubspace H n) (g : AM H n 1),
        g ∈ H.shapePullback W A →
        ¬ (H.shapeSubspaceAction (g.nextCut H)).Large
          (H.shapeGoodTails g (H.shapePullback W A)))
    (W : ShapeSubspace H n) :
    ∃ W' : ShapeSubspace H n,
      FusionStep H m W.1 W'.1 ∧
      ∀ p : AMExact H n m, H.ShapeSettled W' A p.1 := by
  classical
  let P : Finset (AMExact H n m) := Finset.univ
  obtain ⟨W', hstep, hset⟩ :=
    settleExactFinset H hnm A hNo P W
  refine ⟨W', hstep, ?_⟩
  intro p
  exact hset p (by simp [P])

end SMTree
end SuccessorTree
