import SuccessorTree.EnvelopeInvariant
import Mathlib.Tactic

/-!
# Exact level-range invariant for the envelope algorithm

The stage invariant controls the interesting levels inside [i,ell].  This file
adds the tail-fullness which turns that statement into the manuscript's
"skipping exactly" assertion.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- No level above ell is skipped. -/
def TailFull (F : ShapeMap S) (ell : Nat) : Prop :=
  ∀ q : Nat, ell < q → q ∈ F.levelRange

/-- Full stage invariant used in Lemma 5.8. -/
def StageFullInvariant
    (H : SMTree S) (X : Set T) (ell i : Nat)
    (I : Set Nat) (F : MMap H) : Prop :=
  StageInvariant H X ell i I F ∧ TailFull F.map ell

theorem id_levelRange (H : SMTree S) :
    (MMap.id H).map.levelRange = Set.univ := by
  rw [← H.range_levelMap (MMap.id H).map]
  ext q
  simp [MMap.levelMap_id]

/-- Initial stage i=ell. -/
theorem stageFullInvariant_base
    (H : SMTree S) (X : Set T) (ell : Nat) :
    StageFullInvariant H X ell ell {ell} (MMap.id H) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, MMap.id_fixesBelow H ell, ?_⟩
    · intro x hx
      exact ⟨x, rfl⟩
    · ext q
      simp only [representedLevels, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · intro h
        subst q
        refine ⟨?_, le_rfl, le_rfl⟩
        rw [id_levelRange H]
        trivial
      · rintro ⟨_, hle, hge⟩
        omega
  · intro q hq
    rw [id_levelRange H]
    trivial

/-- Interesting stages preserve tail fullness. -/
theorem stageFullInvariant_interesting
    (H : SMTree S) (X : Set T) (ell i : Nat)
    (I : Set Nat) (G : MMap H)
    (hiell : i < ell)
    (hInv : StageFullInvariant H X ell (i + 1) I G) :
    StageFullInvariant H X ell i (insert i I) G := by
  exact ⟨stageInvariant_interesting H X ell i I G hiell hInv.1, hInv.2⟩

/-- Removing level i below ell leaves every target level above ell represented. -/
theorem tailFull_comp_skipsOnly
    (H : SMTree S) (G D : MMap H) (i ell : Nat)
    (hiell : i < ell)
    (hGfix : FixesThrough G.map i)
    (hDskip : D.map.SkipsOnly i)
    (hTail : TailFull G.map ell) :
    TailFull (MMap.comp H G D).map ell := by
  intro q hellq
  rw [levelRange_comp_skipsOnly H G D i hGfix hDskip]
  refine ⟨hTail q hellq, ?_⟩
  intro hqi
  have : q = i := by simpa using hqi
  omega

/-- Noninteresting stages preserve the full invariant. -/
theorem stageFullInvariant_noninteresting
    (H : SMTree S) (hE1 : OneLevelPullback H)
    (X : Set T) (ell i : Nat)
    (hXbound : X ⊆ levelLe ell)
    (I : Set Nat) (G D : MMap H)
    (hiell : i < ell)
    (hInv : StageFullInvariant H X ell (i + 1) I G)
    (hDskip : D.map.SkipsOnly i)
    (hno : ∀ ⦃x : T⦄, x ∈ closure S I X → LevelTree.lev x ≠ i)
    (hDcross :
      ∀ ⦃c : T⦄, c ∈ closure S I X →
        ∀ (hic : i < LevelTree.lev c),
          D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
            LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic)) :
    StageFullInvariant H X ell i I (MMap.comp H G D) := by
  have hThrough : FixesThrough G.map i :=
    fixesThrough_of_fixesBelow_succ H G i hInv.1.2.1
  refine ⟨?_, ?_⟩
  · exact stageInvariant_noninteresting
      H hE1 X ell i hXbound I G D hiell hInv.1 hDskip hno hDcross
  · exact tailFull_comp_skipsOnly
      H G D i ell hiell hThrough hDskip hInv.2

/-- Exact manuscript formulation of the level part of Lemma 5.8. -/
theorem stageFullInvariant_levelRange
    (H : SMTree S) (X : Set T) (ell i : Nat)
    (I : Set Nat) (F : MMap H)
    (hInv : StageFullInvariant H X ell i I F) :
    F.map.levelRange =
      {q | q < i ∨ q ∈ I ∨ ell < q} := by
  rcases hInv with ⟨⟨_hEnv, hFix, hRepresented⟩, hTail⟩
  ext q
  constructor
  · intro hq
    by_cases hqi : q < i
    · exact Or.inl hqi
    by_cases hqell : q ≤ ell
    · have hmid : q ∈ representedLevels F.map i ell :=
        ⟨hq, Nat.le_of_not_gt hqi, hqell⟩
      have hqI : q ∈ I := by
        rw [hRepresented]
        exact hmid
      exact Or.inr (Or.inl hqI)
    · exact Or.inr (Or.inr (Nat.lt_of_not_ge hqell))
  · intro hq
    rcases hq with hbelow | hmidOrTail
    · obtain ⟨x, hx⟩ := H.level_nonempty q
      refine ⟨x, ?_⟩
      have hFx : F x = x := hFix x (by simpa [hx] using hbelow)
      simpa [hFx] using hx
    · rcases hmidOrTail with hqI | htail
      · have hmid : q ∈ representedLevels F.map i ell := by
          rw [← hRepresented]
          exact hqI
        exact hmid.1
      · exact hTail q htail

/-- Equivalently, the skipped levels are exactly the non-interesting levels in
the current interval. -/
theorem stageFullInvariant_skips_iff
    (H : SMTree S) (X : Set T) (ell i q : Nat)
    (I : Set Nat) (F : MMap H)
    (hInv : StageFullInvariant H X ell i I F) :
    F.map.Skips q ↔ i ≤ q ∧ q ≤ ell ∧ q ∉ I := by
  rw [ShapeMap.Skips, stageFullInvariant_levelRange H X ell i I F hInv]
  simp only [Set.mem_ofPred_eq]
  constructor <;> intro h
  · constructor
    · by_contra hqi
      exact h (Or.inl (Nat.lt_of_not_ge hqi))
    · constructor
      · by_contra hqell
        exact h (Or.inr (Or.inr (Nat.lt_of_not_ge hqell)))
      · intro hqI
        exact h (Or.inr (Or.inl hqI))
  · rintro hmem
    rcases hmem with hbelow | hmidOrTail
    · omega
    · rcases hmidOrTail with hqI | htail
      · exact h.2.2 hqI
      · omega

end Envelope
end SMTree
end SuccessorTree
