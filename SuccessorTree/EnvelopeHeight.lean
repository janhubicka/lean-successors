import SuccessorTree.EnvelopeRun
import Mathlib.Tactic

/-!
# Height and minimality of the envelope-algorithm output

This completes the numerical part of Proposition 5.5.  The final selected
target levels are exactly the target levels met before the source preimage of
a top-level member of X.  Hence their number is the height of the output, and
every competing finite-prefix envelope has at least that height.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable {H : SMTree S} {X : Set T} {ell : Nat}

/-- The final selected levels, as a finite set. -/
noncomputable def AlgorithmRun.selectedLevels
    (R : AlgorithmRun H X ell) : Finset Nat := by
  classical
  exact (Finset.range (ell + 1)).filter (fun q => q ∈ R.I 0)

namespace AlgorithmRun

/-- Every final selected level is at most ell. -/
theorem finalLevel_le
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    {q : Nat} (hq : q ∈ R.I 0) :
    q ≤ ell := by
  have hInv := R.fullInvariant hE1 hXbound 0 (Nat.zero_le ell)
  have hrep :
      q ∈ representedLevels (R.F 0).map 0 ell := by
    rw [← hInv.1.2.2]
    exact hq
  exact hrep.2.2

theorem mem_selectedLevels_iff
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (q : Nat) :
    q ∈ R.selectedLevels ↔ q ∈ R.I 0 := by
  classical
  simp only [AlgorithmRun.selectedLevels, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hq⟩
    exact hq
  · intro hq
    exact ⟨Nat.lt_succ_iff.mpr (R.finalLevel_le hE1 hXbound hq), hq⟩

/-- A top-level member of X has a preimage under the final map. -/
theorem exists_top_preimage
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∃ x y : T,
      x ∈ X ∧ LevelTree.lev x = ell ∧ R.F 0 y = x := by
  have hInv := R.fullInvariant hE1 hXbound 0 (Nat.zero_le ell)
  obtain ⟨x, hxX, hxlev⟩ := hTop
  have hxC : x ∈ closure S (R.I 0) X :=
    subset_closure S (R.I 0) X hxX
  obtain ⟨y, hy⟩ := hInv.1.1 hxC
  exact ⟨x, y, hxX, hxlev, hy⟩

/-- The selected target levels are exactly the target levels represented before
and including a source preimage of a top-level member of X. -/
theorem selectedLevels_eq_prefixLevels_of_top_preimage
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    {x y : T}
    (hx : x ∈ X) (hxlev : LevelTree.lev x = ell)
    (hy : R.F 0 y = x) :
    R.selectedLevels =
      prefixLevels H (R.F 0) (LevelTree.lev y + 1) := by
  classical
  have hInv := R.fullInvariant hE1 hXbound 0 (Nat.zero_le ell)
  have htop :
      H.levelMap (R.F 0).map (LevelTree.lev y) = ell := by
    calc
      H.levelMap (R.F 0).map (LevelTree.lev y) =
          LevelTree.lev (R.F 0 y) :=
        H.levelMap_eq (R.F 0).map (a := y)
      _ = LevelTree.lev x := by rw [hy]
      _ = ell := hxlev
  ext q
  rw [R.mem_selectedLevels_iff hE1 hXbound q]
  rw [mem_prefixLevels_iff]
  constructor
  · intro hqI
    have hrep :
        q ∈ representedLevels (R.F 0).map 0 ell := by
      rw [← hInv.1.2.2]
      exact hqI
    have hqRange := hrep.1
    rw [← H.range_levelMap (R.F 0).map] at hqRange
    rcases hqRange with ⟨n, hn⟩
    have hnle : n ≤ LevelTree.lev y := by
      by_contra hnot
      have hyn : LevelTree.lev y < n := Nat.lt_of_not_ge hnot
      have hstrict :=
        H.levelMap_strictMono (R.F 0).map hyn
      rw [hn, htop] at hstrict
      have hqell : q ≤ ell := hrep.2.2
      omega
    exact ⟨n, Nat.lt_succ_iff.mpr hnle, hn⟩
  · rintro ⟨n, hny, hnq⟩
    rw [hInv.1.2.2]
    refine ⟨?_, Nat.zero_le q, ?_⟩
    · rw [← H.range_levelMap (R.F 0).map]
      exact ⟨n, hnq⟩
    · have hnle : n ≤ LevelTree.lev y := Nat.lt_succ_iff.mp hny
      have hmono :=
        (H.levelMap_strictMono (R.F 0).map).monotone hnle
      rw [hnq, htop] at hmono
      exact hmono

/-- The final map already envelopes X inside the source prefix ending at a
preimage of a top-level member. -/
theorem output_prefixEnvelope_of_top_preimage
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    {x y : T}
    (hx : x ∈ X) (hxlev : LevelTree.lev x = ell)
    (hy : R.F 0 y = x) :
    IsPrefixEnvelope (R.F 0).map (LevelTree.lev y + 1) X := by
  have hInv := R.fullInvariant hE1 hXbound 0 (Nat.zero_le ell)
  have htop :
      H.levelMap (R.F 0).map (LevelTree.lev y) = ell := by
    calc
      H.levelMap (R.F 0).map (LevelTree.lev y) =
          LevelTree.lev (R.F 0 y) :=
        H.levelMap_eq (R.F 0).map (a := y)
      _ = LevelTree.lev x := by rw [hy]
      _ = ell := hxlev
  intro z hzX
  have hzC : z ∈ closure S (R.I 0) X :=
    subset_closure S (R.I 0) X hzX
  obtain ⟨w, hw⟩ := hInv.1.1 hzC
  refine ⟨w, ?_, hw⟩
  have hzBound : LevelTree.lev z ≤ ell := hXbound hzX
  have hwmap :
      H.levelMap (R.F 0).map (LevelTree.lev w) =
        LevelTree.lev z := by
    calc
      H.levelMap (R.F 0).map (LevelTree.lev w) =
          LevelTree.lev (R.F 0 w) :=
        H.levelMap_eq (R.F 0).map (a := w)
      _ = LevelTree.lev z := by rw [hw]
  have hwle : LevelTree.lev w ≤ LevelTree.lev y := by
    by_contra hnot
    have hyw : LevelTree.lev y < LevelTree.lev w :=
      Nat.lt_of_not_ge hnot
    have hstrict :=
      H.levelMap_strictMono (R.F 0).map hyw
    rw [hwmap, htop] at hstrict
    omega
  exact Nat.lt_succ_iff.mpr hwle

/-- The height of the produced finite prefix is the number of selected levels. -/
theorem selectedLevels_card_eq_height_of_top_preimage
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    {x y : T}
    (hx : x ∈ X) (hxlev : LevelTree.lev x = ell)
    (hy : R.F 0 y = x) :
    R.selectedLevels.card = LevelTree.lev y + 1 := by
  rw [R.selectedLevels_eq_prefixLevels_of_top_preimage
    hE1 hXbound hx hxlev hy]
  exact card_prefixLevels H (R.F 0) (LevelTree.lev y + 1)

/-- Proposition 5.5, numerical/minimality part, in finite-prefix form. -/
theorem minimal_output_height
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∃ m : Nat,
      IsPrefixEnvelope (R.F 0).map m X ∧
      R.selectedLevels.card = m ∧
      ∀ (E : MMap H) (m' : Nat),
        IsPrefixEnvelope E.map m' X → m ≤ m' := by
  obtain ⟨x, y, hxX, hxlev, hy⟩ :=
    R.exists_top_preimage hE1 hXbound hTop
  let m := LevelTree.lev y + 1
  have hPrefix :
      IsPrefixEnvelope (R.F 0).map m X := by
    exact R.output_prefixEnvelope_of_top_preimage
      hE1 hXbound hxX hxlev hy
  have hCard : R.selectedLevels.card = m := by
    exact R.selectedLevels_card_eq_height_of_top_preimage
      hE1 hXbound hxX hxlev hy
  refine ⟨m, hPrefix, hCard, ?_⟩
  intro E m' hEnvelope
  have hForced :
      ∀ q ∈ R.selectedLevels,
        RepresentedBefore H E.map m' q := by
    intro q hq
    apply R.finalLevels_subset_competitor
      hE1 hXbound hTop E m' hEnvelope
    exact (R.mem_selectedLevels_iff hE1 hXbound q).mp hq
  have hCardLe :=
    card_le_competing_height H E m' R.selectedLevels hForced
  rw [hCard] at hCardLe
  exact hCardLe


/-- A finite approximation is an envelope when its finite source prefix,
equivalently the same prefix of its canonical total representative, covers X. -/
def IsAMEnvelope
    (H : SMTree S) {m : Nat} (a : AM H 0 m) (X : Set T) : Prop :=
  IsPrefixEnvelope (a.representative H).map m X

/-- The minimality theorem also compares directly with every finite
approximation in the manuscript's class AM. -/
theorem minimal_output_height_AM
    (R : AlgorithmRun H X ell)
    (hE1 : OneLevelPullback H)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∃ m : Nat,
      IsPrefixEnvelope (R.F 0).map m X ∧
      R.selectedLevels.card = m ∧
      ∀ (m' : Nat) (a : AM H 0 m'),
        IsAMEnvelope H a X → m ≤ m' := by
  obtain ⟨m, hEnv, hCard, hMin⟩ :=
    R.minimal_output_height hE1 hXbound hTop
  refine ⟨m, hEnv, hCard, ?_⟩
  intro m' a ha
  exact hMin (a.representative H) m' ha

end AlgorithmRun

/-- A finite-approximation envelope is independent of the choice of an
algorithm run. Keep the original qualified name for existing proofs. -/
abbrev IsAMEnvelope
    (H : SMTree S) {m : Nat} (a : AM H 0 m) (X : Set T) : Prop :=
  AlgorithmRun.IsAMEnvelope H a X

end Envelope
end SMTree
end SuccessorTree
