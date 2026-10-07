import SuccessorTree.EnvelopeHeight
import Mathlib.Tactic

/-!
# Existence of envelope-algorithm runs

Algorithm 5.4 makes finitely many classical choices. This file constructs one
such run explicitly, completing the "the algorithm produces" part of the
Section 5 formalisation.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable {H : SMTree S} {X : Set T} {ell : Nat}

/-- If a level is not interesting, the one-level map required by (I3) exists. -/
theorem exists_oneLevel_of_not_interesting
    (H : SMTree S) (C : Set T) (i : Nat)
    (h : ¬ IsInterestingAt H C i) :
    ∃ D : MMap H,
      D.map.SkipsOnly i ∧
      ∀ ⦃z : T⦄, z ∈ C → ∀ (hiz : i < LevelTree.lev z),
        D (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz) := by
  by_contra hnone
  exact h (Or.inr (Or.inr hnone))

/-- State after d downward steps from the top level ell. -/
noncomputable def constructionState
    (H : SMTree S) (X : Set T) (ell : Nat) :
    Nat → Set Nat × MMap H
  | 0 => ({ell}, MMap.id H)
  | d + 1 =>
      let prev := constructionState H X ell d
      let i := ell - (d + 1)
      if h : IsInterestingAt H (closure S prev.1 X) i then
        (insert i prev.1, prev.2)
      else
        let D : MMap H :=
          Classical.choose
            (exists_oneLevel_of_not_interesting H
              (closure S prev.1 X) i h)
        (prev.1, MMap.comp H prev.2 D)

theorem constructionState_succ_interesting
    (H : SMTree S) (X : Set T) (ell d : Nat)
    (h :
      IsInterestingAt H
        (closure S (constructionState H X ell d).1 X)
        (ell - (d + 1))) :
    constructionState H X ell (d + 1) =
      (insert (ell - (d + 1)) (constructionState H X ell d).1,
        (constructionState H X ell d).2) := by
  simp [constructionState, h]

theorem constructionState_succ_noninteresting
    (H : SMTree S) (X : Set T) (ell d : Nat)
    (h :
      ¬ IsInterestingAt H
        (closure S (constructionState H X ell d).1 X)
        (ell - (d + 1))) :
    ∃ D : MMap H,
      D.map.SkipsOnly (ell - (d + 1)) ∧
      (∀ ⦃z : T⦄,
        z ∈ closure S (constructionState H X ell d).1 X →
        ∀ (hiz : ell - (d + 1) < LevelTree.lev z),
          D (LevelTree.ancestor z (ell - (d + 1))
              (Nat.le_of_lt hiz)) =
            LevelTree.ancestor z (ell - (d + 1) + 1)
              (Nat.succ_le_iff.mpr hiz)) ∧
      constructionState H X ell (d + 1) =
        ((constructionState H X ell d).1,
          MMap.comp H (constructionState H X ell d).2 D) := by
  let D : MMap H :=
    Classical.choose
      (exists_oneLevel_of_not_interesting H
        (closure S (constructionState H X ell d).1 X)
        (ell - (d + 1)) h)
  have hD :=
    Classical.choose_spec
      (exists_oneLevel_of_not_interesting H
        (closure S (constructionState H X ell d).1 X)
        (ell - (d + 1)) h)
  refine ⟨D, hD.1, hD.2, ?_⟩
  simp [constructionState, h, D]

noncomputable def constructionI
    (H : SMTree S) (X : Set T) (ell i : Nat) : Set Nat :=
  if i ≤ ell then (constructionState H X ell (ell - i)).1 else ∅

noncomputable def constructionF
    (H : SMTree S) (X : Set T) (ell i : Nat) : MMap H :=
  if i ≤ ell then (constructionState H X ell (ell - i)).2 else MMap.id H

/-- A concrete run of Algorithm 5.4. -/
noncomputable def canonicalAlgorithmRun
    (H : SMTree S) (X : Set T) (ell : Nat) :
    AlgorithmRun H X ell where
  I := constructionI H X ell
  F := constructionF H X ell
  topI := by
    simp [constructionI, constructionState]
  topF := by
    simp [constructionF, constructionState]
  interesting_step := by
    intro i hilt hinter
    have hi : i ≤ ell := Nat.le_of_lt hilt
    have hi1 : i + 1 ≤ ell := Nat.succ_le_iff.mpr hilt
    let d := ell - (i + 1)
    have hdist : ell - i = d + 1 := by
      dsimp [d]
      omega
    have hidx : ell - (d + 1) = i := by
      dsimp [d]
      omega
    have hinter' :
        IsInterestingAt H
          (closure S (constructionState H X ell d).1 X) i := by
      simpa [constructionI, hi1, d] using hinter
    have hstep :=
      constructionState_succ_interesting H X ell d (by
        simpa [hidx] using hinter')
    constructor
    · simp only [constructionI, if_pos hi, if_pos hi1]
      rw [hdist, hstep]
      simp [d]
    · simp only [constructionF, if_pos hi, if_pos hi1]
      rw [hdist, hstep]
      simp [d]
  noninteresting_step := by
    intro i hilt hinter
    have hi : i ≤ ell := Nat.le_of_lt hilt
    have hi1 : i + 1 ≤ ell := Nat.succ_le_iff.mpr hilt
    let d := ell - (i + 1)
    have hdist : ell - i = d + 1 := by
      dsimp [d]
      omega
    have hidx : ell - (d + 1) = i := by
      dsimp [d]
      omega
    have hinter' :
        ¬ IsInterestingAt H
          (closure S (constructionState H X ell d).1 X) i := by
      simpa [constructionI, hi1, d] using hinter
    obtain ⟨D, hDskip0, hDcross0, hstep⟩ :=
      constructionState_succ_noninteresting H X ell d (by
        simpa [hidx] using hinter')
    have hDskip : D.map.SkipsOnly i := by
      simpa [hidx] using hDskip0
    have hDcross :
        ∀ ⦃c : T⦄,
          c ∈ closure S (constructionI H X ell (i + 1)) X →
          ∀ (hic : i < LevelTree.lev c),
            D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
              LevelTree.ancestor c (i + 1)
                (Nat.succ_le_iff.mpr hic) := by
      intro c hc hic
      have hc' :
          c ∈ closure S (constructionState H X ell d).1 X := by
        simpa [constructionI, hi1, d] using hc
      have h0 := hDcross0 hc'
        (by simpa [hidx] using hic)
      simpa [hidx] using h0
    refine ⟨D, hDskip, hDcross, ?_, ?_⟩
    · simp only [constructionI, if_pos hi, if_pos hi1]
      rw [hdist, hstep]
      simp [d]
    · simp only [constructionF, if_pos hi, if_pos hi1]
      rw [hdist, hstep]
      simp [d]

/-- Algorithm 5.4 always has a run. -/
theorem algorithmRun_nonempty
    (H : SMTree S) (X : Set T) (ell : Nat) :
    Nonempty (AlgorithmRun H X ell) :=
  ⟨canonicalAlgorithmRun H X ell⟩

end Envelope
end SMTree
end SuccessorTree
