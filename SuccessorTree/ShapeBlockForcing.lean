import SuccessorTree.ShapeAction
import Mathlib.Tactic

/-!
# Finite shape blocks and the maximal-avoider fusion

A finite k-variable shape block is represented by AM^n_{k+1}: its first
moving level is the finite "head", followed by k further source levels.
It acts on a one-level word g whenever the image of g stays inside the
finite source segment recorded by the block.

This file proves the shape analogue of the maximal-avoider lemma from the
combinatorial-forcing proof of Hales--Jewett.  The only infinitary input is
M1 fusion.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- One more source level extends a finite shape block. -/
def BlockExtends
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) (h' : AM H n (k + 2)) : Prop :=
  ∀ x : InitialNode T (n + k),
    h.1.1 x =
      h'.1.1 ⟨x.1, x.2.trans (Nat.le_succ (n + k))⟩

/-- Representatives of two extending blocks agree throughout the shorter
finite source segment. -/
theorem blockExtends_representative_agrees
    (H : SMTree S) {n k : Nat}
    {h : AM H n (k + 1)} {h' : AM H n (k + 2)}
    (hext : BlockExtends H h h')
    (x : T) (hx : LevelTree.lev x ≤ n + k) :
    h.representative H x = h'.representative H x := by
  let xx : InitialNode T (n + k) := ⟨x, hx⟩
  have htop := h.representative_top H
  have htop' := h'.representative_top H
  have hv := congrArg Subtype.val htop
  have hv' := congrArg Subtype.val htop'
  change
    (h.representative H).restrictLe H (n + k) = h.1.1 at hv
  change
    (h'.representative H).restrictLe H (n + k + 1) = h'.1.1 at hv'
  calc
    h.representative H x = h.1.1 xx := congrFun hv xx
    _ = h'.1.1
        ⟨x, hx.trans (Nat.le_succ (n + k))⟩ := hext xx
    _ = h'.representative H x := by
      exact (congrFun hv'
        ⟨x, hx.trans (Nat.le_succ (n + k))⟩).symm

/-- The total representative of a finite block, viewed as a shape subspace
at the original frozen cut n. -/
noncomputable def blockSubspace
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) : ShapeSubspace H n :=
  ⟨h.representative H, h.representative_fixesBelow H⟩

/-- Evaluate a finite shape block on a one-level word. -/
noncomputable def blockEval
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) (g : AM H n 1) : AM H n 1 :=
  H.shapeAct n (H.blockSubspace h) g

/-- Extending the block cannot change its evaluation on an input whose
terminal target level is still inside the shorter recorded source segment. -/
theorem blockEval_eq_of_extends
    (H : SMTree S) {n k : Nat}
    {h : AM H n (k + 1)} {h' : AM H n (k + 2)}
    (hext : BlockExtends H h h')
    (g : AM H n 1)
    (hg : g.topLevel H < n + k + 1) :
    H.blockEval h g = H.blockEval h' g := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hy :
      LevelTree.lev (g.representative H x.1) ≤ n + k := by
    have hle :=
      g.level_le_topLevel H x.1 x.2
    omega
  change
    h.representative H (g.representative H x.1) =
      h'.representative H (g.representative H x.1)
  exact H.blockExtends_representative_agrees hext
    (g.representative H x.1) hy

/-- A k-variable block avoids A when all evaluations whose terminal level
fits in the block avoid A. -/
def BlockAvoids
    (H : SMTree S) {n k : Nat}
    (A : Set (AM H n 1))
    (h : AM H n (k + 1)) : Prop :=
  ∀ g : AMBelow H n (n + k + 1), H.blockEval h g.1 ∉ A

/-- The identity input evaluates a one-level block to the block itself. -/
theorem blockEval_id1
    (H : SMTree S) {n : Nat} (h : AM H n 1) :
    H.blockEval h (AM.id1 H n) = h := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have hh := h.representative_top H
  have hv := congrArg Subtype.val hh
  change (h.representative H).restrictLe H n = h.1.1 at hv
  have hx := congrFun hv x
  change
    h.representative H
        ((AM.id1 H n).representative H x.1) =
      h.1.1 x
  have hid :
      (AM.id1 H n).representative H x.1 = x.1 := by
    have htop := (AM.id1 H n).representative_top H
    have hval := congrArg Subtype.val htop
    change
      ((AM.id1 H n).representative H).restrictLe H n =
        (MMap.id H).restrictLe H n at hval
    exact congrFun hval x
  rw [hid]
  exact hx

/-- A word outside A is a 0-variable avoiding block. -/
theorem blockAvoids_zero_of_not_mem
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (h : AM H n 1) (hh : h ∉ A) :
    BlockAvoids H (k := 0) A h := by
  intro g
  have gid : g.1 = AM.id1 H n := by
    apply AM.eq_id1_of_topLevel_le H g.1
    omega
  rw [gid, H.blockEval_id1]
  exact hh

/-- The total representative gives a canonical one-source-level extension
of any finite block. -/
noncomputable def blockCanonicalExtension
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) : AM H n (k + 2) :=
  (h.representative H).toAM H n (k + 2)
    (h.representative_fixesBelow H)

theorem blockCanonicalExtension_extends
    (H : SMTree S) {n k : Nat}
    (h : AM H n (k + 1)) :
    BlockExtends H h (H.blockCanonicalExtension h) := by
  intro x
  have htop := h.representative_top H
  have hv := congrArg Subtype.val htop
  change
    (h.representative H).restrictLe H (n + k) = h.1.1 at hv
  have hx := congrFun hv x
  change
    h.1.1 x = h.representative H x.1
  exact hx.symm

/-- An avoiding block bundled with its dimension. -/
structure AvoidingBlock
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1)) (k : Nat) where
  word : AM H n (k + 1)
  avoids : BlockAvoids H A word

/-- Chosen avoiding extension, under the hypothesis that every avoiding block
has one. -/
noncomputable def avoidingBlockNext
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h')
    {k : Nat} (X : AvoidingBlock H A k) :
    AvoidingBlock H A (k + 1) := by
  let h' := Classical.choose (extendable k X)
  exact ⟨h',
    (Classical.choose_spec (extendable k X)).2⟩

theorem avoidingBlockNext_extends
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h')
    {k : Nat} (X : AvoidingBlock H A k) :
    BlockExtends H X.word
      (H.avoidingBlockNext A extendable X).word :=
  (Classical.choose_spec (extendable k X)).1

/-- Greedy chain of avoiding blocks. -/
noncomputable def avoidingBlockSeq
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h') :
    (k : Nat) → AvoidingBlock H A k
  | 0 => X0
  | k + 1 =>
      H.avoidingBlockNext A extendable
        (H.avoidingBlockSeq A X0 extendable k)

/-- Consecutive greedy blocks extend one another. -/
theorem avoidingBlockSeq_extends
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h')
    (k : Nat) :
    BlockExtends H
      (H.avoidingBlockSeq A X0 extendable k).word
      (H.avoidingBlockSeq A X0 extendable (k + 1)).word := by
  change BlockExtends H
    (H.avoidingBlockSeq A X0 extendable k).word
    (H.avoidingBlockNext A extendable
      (H.avoidingBlockSeq A X0 extendable k)).word
  exact H.avoidingBlockNext_extends A extendable
    (H.avoidingBlockSeq A X0 extendable k)

/-- Reindex the greedy block representatives by tree level, padding below n
with the first block. -/
noncomputable def avoidingFusionStage
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h')
    (i : Nat) : MMap H :=
  (H.avoidingBlockSeq A X0 extendable (i - n)).word.representative H

theorem avoidingFusionStage_stable
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h') :
    ShapeMap.FusionStable
      (fun i => (H.avoidingFusionStage A X0 extendable i).map) := by
  intro i x hx
  by_cases hin : i < n
  · have hi0 : i - n = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hin)
    have hisucc0 : (i + 1) - n = 0 := by omega
    change
      (H.avoidingBlockSeq A X0 extendable (i - n)).word.representative H x =
        (H.avoidingBlockSeq A X0 extendable ((i + 1) - n)).word.representative H x
    rw [hi0, hisucc0]
  · have hni : n ≤ i := Nat.le_of_not_gt hin
    let k := i - n
    have hik : i = n + k := by
      dsimp [k]
      omega
    have hiIndex : i - n = k := rfl
    have hisucc : (i + 1) - n = k + 1 := by
      dsimp [k]
      omega
    have hext :=
      H.avoidingBlockSeq_extends A X0 extendable k
    change
      (H.avoidingBlockSeq A X0 extendable (i - n)).word.representative H x =
        (H.avoidingBlockSeq A X0 extendable ((i + 1) - n)).word.representative H x
    rw [hiIndex, hisucc]
    apply H.blockExtends_representative_agrees hext
    rw [← hik]
    exact hx

/-- The M1 fusion limit of the greedy avoiding chain. -/
noncomputable def avoidingFusionLimit
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h') :
    MMap H where
  map :=
    ShapeMap.fusionLimit
      (fun i => (H.avoidingFusionStage A X0 extendable i).map)
      (H.avoidingFusionStage_stable A X0 extendable)
  mem :=
    H.fusion_mem
      (fun i => (H.avoidingFusionStage A X0 extendable i).map)
      (fun i => (H.avoidingFusionStage A X0 extendable i).mem)
      (H.avoidingFusionStage_stable A X0 extendable)

/-- The avoiding fusion is a shape subspace at the original frozen cut. -/
theorem avoidingFusionLimit_fixesBelow
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h') :
    (H.avoidingFusionLimit A X0 extendable).FixesBelow H n := by
  intro x hx
  change
    H.avoidingFusionStage A X0 extendable (LevelTree.lev x) x = x
  have hi0 : LevelTree.lev x - n = 0 := by omega
  unfold avoidingFusionStage
  rw [hi0]
  exact
    (H.avoidingBlockSeq A X0 extendable 0).word.representative_fixesBelow
      H x hx

/-- On every bounded target segment, the fusion limit agrees with the
corresponding greedy block. -/
theorem avoidingFusionLimit_agrees_block
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h')
    (k : Nat) (x : T)
    (hx : LevelTree.lev x ≤ n + k) :
    H.avoidingFusionLimit A X0 extendable x =
      (H.avoidingBlockSeq A X0 extendable k).word.representative H x := by
  let stages := fun i =>
    (H.avoidingFusionStage A X0 extendable i).map
  let hstable := H.avoidingFusionStage_stable A X0 extendable
  change ShapeMap.fusionLimit stages hstable x =
    (H.avoidingBlockSeq A X0 extendable k).word.representative H x
  calc
    ShapeMap.fusionLimit stages hstable x =
        stages (n + k) x :=
      ShapeMap.fusionLimit_eq_stage stages hstable hx
    _ = (H.avoidingBlockSeq A X0 extendable k).word.representative H x := by
      have hidx : n + k - n = k := by omega
      change
        (H.avoidingBlockSeq A X0 extendable (n + k - n)).word.representative H x =
          (H.avoidingBlockSeq A X0 extendable k).word.representative H x
      rw [hidx]

/-- If every avoiding block extended, the fusion limit would avoid A on every
one-level word. -/
theorem avoidingFusionLimit_avoids
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (X0 : AvoidingBlock H A 0)
    (extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h')
    (g : AM H n 1) :
    H.shapeAct n
      ⟨H.avoidingFusionLimit A X0 extendable,
        H.avoidingFusionLimit_fixesBelow A X0 extendable⟩ g ∉ A := by
  let k := g.topLevel H + 1
  have hg : g.topLevel H < n + k + 1 := by
    dsimp [k]
    omega
  let Xk := H.avoidingBlockSeq A X0 extendable k
  have havoid := Xk.avoids
    (⟨g, hg⟩ : AMBelow H n (n + k + 1))
  have heq :
      H.shapeAct n
          ⟨H.avoidingFusionLimit A X0 extendable,
            H.avoidingFusionLimit_fixesBelow A X0 extendable⟩ g =
        H.blockEval Xk.word g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hy :
        LevelTree.lev (g.representative H x.1) ≤ n + k := by
      have hle := g.level_le_topLevel H x.1 x.2
      dsimp [k]
      omega
    change
      H.avoidingFusionLimit A X0 extendable
          (g.representative H x.1) =
        Xk.word.representative H (g.representative H x.1)
    exact H.avoidingFusionLimit_agrees_block
      A X0 extendable k (g.representative H x.1) hy
  rw [heq]
  exact havoid

/-- Largeness forces the greedy avoiding construction to stop at a finite
maximal avoiding block. -/
theorem exists_maximal_avoidingBlock_of_large
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (hlarge : (H.shapeSubspaceAction n).Large A)
    (h0 : AM H n 1) (hh0 : h0 ∉ A) :
    ∃ k : Nat, ∃ h : AM H n (k + 1),
      BlockAvoids H A h ∧
      ∀ h' : AM H n (k + 2),
        BlockExtends H h h' →
        ¬ BlockAvoids H A h' := by
  let X0 : AvoidingBlock H A 0 :=
    ⟨h0, H.blockAvoids_zero_of_not_mem A h0 hh0⟩
  classical
  by_contra hnone
  have extendable :
      ∀ k (X : AvoidingBlock H A k),
        ∃ h' : AM H n (k + 2),
          BlockExtends H X.word h' ∧
          BlockAvoids H A h' := by
    intro k X
    by_contra hext
    have hmax :
        ∀ h' : AM H n (k + 2),
          BlockExtends H X.word h' →
          ¬ BlockAvoids H A h' := by
      intro h' hh'
      intro hav
      exact hext ⟨h', hh', hav⟩
    exact hnone ⟨k, X.word, X.avoids, hmax⟩
  let L : ShapeSubspace H n :=
    ⟨H.avoidingFusionLimit A X0 extendable,
      H.avoidingFusionLimit_fixesBelow A X0 extendable⟩
  obtain ⟨g, hg⟩ := hlarge L
  exact (H.avoidingFusionLimit_avoids A X0 extendable g) hg

end SMTree
end SuccessorTree
