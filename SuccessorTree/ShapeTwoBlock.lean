import SuccessorTree.ShapeDirectLine
import Mathlib.Tactic

/-!
# Factoring a two-level shape block into a head and a tail

Every h in AM^n_2 has a canonical first one-moving level g in AM^n_1.
M2/canonical factorisation then supplies one tail coordinate q based at the
next cut of g.  Evaluating h on the local identity/one-level letters is
exactly the algebraic line shapeLineApply g q.

This is the bridge from the finite two-level pigeonhole witness to the
good-tail language used by the Milliken fusion.
-/

namespace SuccessorTree
namespace SMTree

open SuccessorTree.HalesJewett

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- First one-moving level of a two-level block. -/
noncomputable def twoBlockHead
    (H : SMTree S) {n : Nat}
    (h : AM H n 2) : AM H n 1 :=
  (h.representative H).toAM H n 1 h.representative_fixesBelow

theorem twoBlockHead_topLevel
    (H : SMTree S) {n : Nat}
    (h : AM H n 2) :
    (H.twoBlockHead h).topLevel H =
      H.levelMap (h.representative H).map n :=
  MMap.toAM_one_topLevel H (h.representative H) n
    h.representative_fixesBelow

/-- The canonical extension of the chosen head is the canonical extension of
the original two-level representative through its first moving source level. -/
theorem twoBlockHead_canonical
    (H : SMTree S) {n : Nat}
    (h : AM H n 2) :
    (H.twoBlockHead h).canonical H =
      H.canonicalExtension (h.representative H) n := by
  let K := h.representative H
  let g := H.twoBlockHead h
  have hagree :
      ∀ x : T, LevelTree.lev x ≤ n → g.representative H x = K x := by
    intro x hx
    exact MMap.toAM_one_representative_agrees
      H K n h.representative_fixesBelow x hx
  apply H.canonicalExtension_unique K (g.canonical H) n
  · intro x hx
    rw [AM.canonical, H.canonicalExtension_agrees
      (g.representative H) n x hx]
    exact hagree x hx
  · intro ell hell
    apply H.canonicalExtension_tail_mem_levelRange
      (g.representative H) n ell
    have htop :
        H.levelMap (g.representative H).map n =
          H.levelMap K.map n := by
      obtain ⟨x, hx⟩ := H.level_nonempty n
      calc
        H.levelMap (g.representative H).map n =
            LevelTree.lev (g.representative H x) := by
          simpa [hx] using H.levelMap_eq (g.representative H).map (a := x)
        _ = LevelTree.lev (K x) := by rw [hagree x (by simpa [hx])]
        _ = H.levelMap K.map n := by
          simpa [hx] using (H.levelMap_eq K.map (a := x)).symm
    exact htop.trans_le hell

/-- Chosen outer factor after the first canonical level of a two-level block. -/
noncomputable def twoBlockTailMap
    (H : SMTree S) {n : Nat}
    (h : AM H n 2) : MMap H :=
  Classical.choose
    (H.exists_factor_through_canonical_succ (h.representative H) n)

theorem twoBlockTailMap_spec
    (H : SMTree S) {n : Nat}
    (h : AM H n 2) :
    let Q := H.twoBlockTailMap h
    Q.FixesBelow H ((H.twoBlockHead h).nextCut H) ∧
      ∀ x : T, LevelTree.lev x ≤ n + 1 →
        Q ((H.twoBlockHead h).canonical H x) =
          h.representative H x := by
  let K := h.representative H
  let g := H.twoBlockHead h
  have hs :=
    Classical.choose_spec
      (H.exists_factor_through_canonical_succ K n)
  rcases hs with ⟨hfix, hlev, hagree⟩
  have hnext :
      g.nextCut H = H.levelMap K.map n + 1 := by
    unfold AM.nextCut
    rw [H.twoBlockHead_topLevel h]
  refine ⟨?_, ?_⟩
  · rw [hnext]
    exact hfix
  · intro x hx
    change
      H.twoBlockTailMap h (g.canonical H x) = K x
    have hcan := H.twoBlockHead_canonical h
    rw [hcan]
    exact hagree x hx

/-- Tail coordinate of the two-level block. -/
noncomputable def twoBlockTail
    (H : SMTree S) {n : Nat}
    (h : AM H n 2) :
    AM H ((H.twoBlockHead h).nextCut H) 1 :=
  (H.twoBlockTailMap h).toAM H
    ((H.twoBlockHead h).nextCut H) 1
    (H.twoBlockTailMap_spec h).1

theorem twoBlockTail_representative_agrees
    (H : SMTree S) {n : Nat}
    (h : AM H n 2)
    (x : T)
    (hx : LevelTree.lev x ≤ (H.twoBlockHead h).nextCut H) :
    (H.twoBlockTail h).representative H x =
      H.twoBlockTailMap h x := by
  exact MMap.toAM_one_representative_agrees
    H (H.twoBlockTailMap h) ((H.twoBlockHead h).nextCut H)
      (H.twoBlockTailMap_spec h).1 x hx

/-- A two-level block evaluates exactly as the algebraic line through its
canonical head and tail. -/
theorem blockEval_twoBlock_line
    (H : SMTree S) {n : Nat}
    (h : AM H n 2)
    (p : LineInput (OneLevelLetter H n)) :
    H.blockEval h (H.lineInputAM n p) =
      H.shapeLineApply (H.twoBlockHead h) (H.twoBlockTail h) p := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  let K := h.representative H
  let g := H.twoBlockHead h
  let Q := H.twoBlockTailMap h
  have hp :
      (H.lineInputAM n p).representative H x.1 =
        localInputMMap H n p x.1 :=
    H.lineInputAM_representative_agrees n p x.1 x.2
  have hlocal :
      LevelTree.lev (localInputMMap H n p x.1) ≤ n + 1 := by
    cases p with
    | base =>
        change LevelTree.lev x.1 ≤ n + 1
        omega
    | letter e =>
        change LevelTree.lev (e.toMMap x.1) ≤ n + 1
        rw [e.level_apply H]
        split <;> omega
  have hcanBound :
      LevelTree.lev
          ((H.twoBlockHead h).canonical H
            (localInputMMap H n p x.1)) ≤
        (H.twoBlockHead h).nextCut H := by
    calc
      LevelTree.lev
          ((H.twoBlockHead h).canonical H
            (localInputMMap H n p x.1)) =
          H.levelMap ((H.twoBlockHead h).canonical H).map
            (LevelTree.lev (localInputMMap H n p x.1)) :=
        (H.levelMap_eq ((H.twoBlockHead h).canonical H).map
          (a := localInputMMap H n p x.1)).symm
      _ ≤ H.levelMap ((H.twoBlockHead h).canonical H).map (n + 1) :=
        (H.levelMap_strictMono ((H.twoBlockHead h).canonical H).map).monotone
          hlocal
      _ = (H.twoBlockHead h).nextCut H :=
        (H.twoBlockHead h).canonical_level_next H
  have hq :
      (H.twoBlockTail h).representative H
          ((H.twoBlockHead h).canonical H
            (localInputMMap H n p x.1)) =
        Q ((H.twoBlockHead h).canonical H
            (localInputMMap H n p x.1)) :=
    H.twoBlockTail_representative_agrees h _ hcanBound
  have hfactor :=
    (H.twoBlockTailMap_spec h).2
      (localInputMMap H n p x.1) hlocal
  change
    K ((H.lineInputAM n p).representative H x.1) =
      (H.twoBlockTail h).representative H
        ((H.twoBlockHead h).canonical H
          (localInputMMap H n p x.1))
  rw [hp, hq]
  exact hfactor.symm

/-- The local line of any two-level block is witnessed by one good tail. -/
theorem twoBlockTail_mem_goodTails
    (H : SMTree S) {n : Nat}
    (A : Set (AM H n 1))
    (h : AM H n 2)
    (hline :
      ∀ p : LineInput (OneLevelLetter H n),
        H.blockEval h (H.lineInputAM n p) ∈ A) :
    H.twoBlockTail h ∈
      H.shapeGoodTails (H.twoBlockHead h) A := by
  intro p
  rw [← H.blockEval_twoBlock_line h p]
  exact hline p

end SMTree
end SuccessorTree
