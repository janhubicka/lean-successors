import SuccessorTree.EnvelopeStage
import SuccessorTree.Canonical
import Mathlib.Tactic

/-!
# The envelope-algorithm invariant, one stage at a time

This file isolates the two induction steps in Lemma 5.8. The recursive driver
of Algorithm 5.4 can then be kept separate from the mathematical invariant.
Only the canonical-map infrastructure is needed here, not the Ramsey engine.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- E1 in the form actually used by the envelope proof. -/
def OneLevelPullback (H : SMTree S) : Prop :=
  ∀ (D : MMap H) (m : Nat), D.map.SkipsOnly m → PullbackDefined S D.map

/-- The levels represented by an admissible map inside the interval [i,ell]. -/
def representedLevels
    (F : ShapeMap S) (i ell : Nat) : Set Nat :=
  {q | q ∈ F.levelRange ∧ i ≤ q ∧ q ≤ ell}

/-- The invariant needed at stage i of Algorithm 5.4. -/
def StageInvariant
    (H : SMTree S) (X : Set T) (ell i : Nat)
    (I : Set Nat) (F : MMap H) : Prop :=
  IsEnvelope F.map (closure S I X) ∧
  F.FixesBelow H i ∧
  I = representedLevels F.map i ell

theorem fixesThrough_of_fixesBelow_succ
    (H : SMTree S) (F : MMap H) (i : Nat)
    (hfix : F.FixesBelow H (i + 1)) :
    FixesThrough F.map i := by
  intro x hx
  exact hfix x (by omega)

theorem level_mem_range_of_fixesThrough
    (H : SMTree S) (F : ShapeMap S) (i : Nat)
    (hfix : FixesThrough F i) :
    i ∈ F.levelRange := by
  obtain ⟨x, hx⟩ := H.level_nonempty i
  refine ⟨x, ?_⟩
  rw [hfix (by simpa [hx])]
  exact hx

/-- Composing on the right by a one-level skip removes exactly that target
level, provided the outer map fixes it. -/
theorem levelRange_comp_skipsOnly
    (H : SMTree S) (G D : MMap H) (m : Nat)
    (hG : FixesThrough G.map m)
    (hD : D.map.SkipsOnly m) :
    (MMap.comp H G D).map.levelRange =
      G.map.levelRange \ {m} := by
  have hGm : H.levelMap G.map m = m := by
    obtain ⟨x, hx⟩ := H.level_nonempty m
    calc
      H.levelMap G.map m = LevelTree.lev (G x) := by
        simpa [hx] using H.levelMap_eq G.map (a := x)
      _ = LevelTree.lev x := by
        rw [hG (by simpa [hx])]
      _ = m := hx
  rw [← H.range_levelMap (MMap.comp H G D).map]
  rw [← H.range_levelMap G.map]
  ext q
  constructor
  · rintro ⟨n, hn⟩
    rw [MMap.levelMap_comp] at hn
    refine ⟨⟨H.levelMap D.map n, hn⟩, ?_⟩
    intro hqm
    have hDm : H.levelMap D.map n = m := by
      apply (H.levelMap_strictMono G.map).injective
      rw [hn, hGm]
      exact hqm
    have hmRange : m ∈ D.map.levelRange := by
      rw [← H.range_levelMap D.map]
      exact ⟨n, hDm⟩
    rw [hD] at hmRange
    exact hmRange rfl
  · rintro ⟨⟨k, hk⟩, hkne⟩
    have hkm : k ≠ m := by
      intro h
      subst k
      rw [hGm] at hk
      apply hkne
      simpa using hk.symm
    have hkRange : k ∈ D.map.levelRange := by
      rw [hD]
      exact hkm
    rw [← H.range_levelMap D.map] at hkRange
    rcases hkRange with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [MMap.levelMap_comp, hn, hk]

theorem representedLevels_comp_skipsOnly
    (H : SMTree S) (G D : MMap H) (i ell : Nat)
    (hGfix : FixesThrough G.map i)
    (hDskip : D.map.SkipsOnly i) :
    representedLevels (MMap.comp H G D).map i ell =
      representedLevels G.map (i + 1) ell := by
  rw [representedLevels, representedLevels,
    levelRange_comp_skipsOnly H G D i hGfix hDskip]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hq, hqi⟩, hiq, hqell⟩
    exact ⟨hq, by omega, hqell⟩
  · rintro ⟨hq, hiq, hqell⟩
    exact ⟨⟨hq, by omega⟩, by omega, hqell⟩

/-- Restrict a FixesBelow witness to an earlier cut. -/
theorem fixesBelow_mono
    (H : SMTree S) (F : MMap H) {i j : Nat}
    (hij : i ≤ j) (hF : F.FixesBelow H j) :
    F.FixesBelow H i := by
  intro x hx
  exact hF x (lt_of_lt_of_le hx hij)

/-- A map skipping only i fixes every source level strictly below i. -/
theorem fixesBelow_of_skipsOnly
    (H : SMTree S) (D : MMap H) (i : Nat)
    (hD : D.map.SkipsOnly i) :
    D.FixesBelow H i := by
  intro x hx
  exact H.eq_id_below_skip D.map i hD hx

/-- The interesting branch of Lemma 5.8. -/
theorem stageInvariant_interesting
    (H : SMTree S) (X : Set T) (ell i : Nat)
    (I : Set Nat) (G : MMap H)
    (hiell : i < ell)
    (hInv : StageInvariant H X ell (i + 1) I G) :
    StageInvariant H X ell i (insert i I) G := by
  rcases hInv with ⟨hEnv, hFix, hRange⟩
  have hThrough : FixesThrough G.map i :=
    fixesThrough_of_fixesBelow_succ H G i hFix
  have hiRange : i ∈ G.map.levelRange :=
    level_mem_range_of_fixesThrough H G.map i hThrough
  have hISub : I ⊆ G.map.levelRange := by
    intro q hq
    rw [hRange] at hq
    exact hq.1
  refine ⟨?_, fixesBelow_mono H G (by omega) hFix, ?_⟩
  · apply envelope_closure H G.map
      (X := X) (I := insert i I)
    · intro x hx
      exact hEnv (subset_closure S I X hx)
    · intro q hq
      rcases hq with rfl | hq
      · exact hiRange
      · exact hISub hq
  · rw [hRange]
    ext q
    simp only [Set.mem_insert_iff, representedLevels, Set.mem_ofPred_eq]
    constructor
    · intro hq
      rcases hq with rfl | hq
      · exact ⟨hiRange, le_rfl, Nat.le_of_lt hiell⟩
      · exact ⟨hq.1, by omega, hq.2.2⟩
    · rintro ⟨hqRange, hiq, hqell⟩
      by_cases hqi : q = i
      · exact Or.inl hqi
      · exact Or.inr ⟨hqRange, by omega, hqell⟩

/-- The noninteresting branch of Lemma 5.8. The hypotheses `hno`, `hDcross`
and `hDskip` are exactly the data supplied when (I1), (I2), (I3) all fail. -/
theorem stageInvariant_noninteresting
    (H : SMTree S) (hE1 : OneLevelPullback H)
    (X : Set T) (ell i : Nat)
    (hXbound : X ⊆ levelLe ell)
    (I : Set Nat) (G D : MMap H)
    (hiell : i < ell)
    (hInv : StageInvariant H X ell (i + 1) I G)
    (hDskip : D.map.SkipsOnly i)
    (hno : ∀ ⦃x : T⦄, x ∈ closure S I X → LevelTree.lev x ≠ i)
    (hDcross :
      ∀ ⦃c : T⦄, c ∈ closure S I X →
        ∀ (hic : i < LevelTree.lev c),
          D (LevelTree.ancestor c i (Nat.le_of_lt hic)) =
            LevelTree.ancestor c (i + 1) (Nat.succ_le_iff.mpr hic)) :
    StageInvariant H X ell i I (MMap.comp H G D) := by
  rcases hInv with ⟨hEnv, hFix, hRange⟩
  let C : Set T := closure S I X
  have hThrough : FixesThrough G.map i :=
    fixesThrough_of_fixesBelow_succ H G i hFix
  have hBound : C ⊆ levelLe ell :=
    closure_subset_levelLe I X ell hXbound
  have hIndexed :
      ∀ ⦃q : Nat⦄, q ∈ G.map.levelRange →
        i < q → q ≤ ell → q ∈ I := by
    intro q hq hiq hqell
    rw [hRange]
    exact ⟨hq, by omega, hqell⟩
  have hPre :
      G ⁻¹' C ⊆ Set.range D := by
    exact preimage_subset_range_of_bounded_indexed
      H G.map D.map i ell hThrough hDskip (hE1 D i hDskip)
      C I (closure_parameterClosed S I X) hBound hIndexed hno hDcross
  have hNewEnv : IsEnvelope (MMap.comp H G D).map C := by
    intro c hc
    obtain ⟨a, ha⟩ := hEnv hc
    have haC : a ∈ G ⁻¹' C := by
      change G a ∈ C
      simpa [ha] using hc
    obtain ⟨b, hb⟩ := hPre haC
    refine ⟨b, ?_⟩
    change G (D b) = c
    rw [hb, ha]
  have hDFix : D.FixesBelow H i :=
    fixesBelow_of_skipsOnly H D i hDskip
  refine ⟨hNewEnv, ?_, ?_⟩
  · exact MMap.comp_fixesBelow H G D i
      (fixesBelow_mono H G (by omega) hFix) hDFix
  · calc
      I = representedLevels G.map (i + 1) ell := hRange
      _ = representedLevels (MMap.comp H G D).map i ell :=
        (representedLevels_comp_skipsOnly H G D i ell hThrough hDskip).symm

end Envelope
end SMTree
end SuccessorTree
