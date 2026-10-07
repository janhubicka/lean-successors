import SuccessorTree.EnvelopePrefix
import SuccessorTree.EnvelopeMinimal
import Mathlib.Tactic

/-!
# Minimality core for envelope interesting levels

This file proves the local contradiction used in Proposition 5.5 against a
competing finite-prefix envelope.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Target level i occurs among the first m source levels of F. -/
def RepresentedBefore (H : SMTree S) (F : ShapeMap S)
    (m i : Nat) : Prop :=
  ∃ n < m, H.levelMap F n = i

theorem representedBefore_iff_level_prefixRange
    (H : SMTree S) (F : ShapeMap S) (m i : Nat) :
    RepresentedBefore H F m i ↔
      ∃ x ∈ prefixRange F m, LevelTree.lev x = i := by
  constructor
  · rintro ⟨n, hnm, hn⟩
    obtain ⟨x, hx⟩ := H.level_nonempty n
    refine ⟨F x, ⟨x, (by simpa [hx] using hnm), rfl⟩, ?_⟩
    calc
      LevelTree.lev (F x) = H.levelMap F n := by
        simpa [hx] using (H.levelMap_eq F (a := x)).symm
      _ = i := hn
  · rintro ⟨x, ⟨y, hym, rfl⟩, hlev⟩
    refine ⟨LevelTree.lev y, hym, ?_⟩
    exact (H.levelMap_eq F (a := y)).trans hlev

/-- A node on level i in a prefix-enveloped set forces i to be represented
inside that prefix. -/
theorem representedBefore_of_node
    (H : SMTree S) (F : ShapeMap S) (m i : Nat)
    {C : Set T} (hC : IsPrefixEnvelope F m C)
    {x : T} (hxC : x ∈ C) (hx : LevelTree.lev x = i) :
    RepresentedBefore H F m i := by
  rw [representedBefore_iff_level_prefixRange H F m i]
  exact ⟨x, hC hxC, hx⟩

/-- Likewise a meet on level i forces i to be represented, provided the set
is meet-closed. -/
theorem representedBefore_of_meet
    (H : SMTree S) (F : ShapeMap S) (m i : Nat)
    {C : Set T} (hC : IsPrefixEnvelope F m C)
    (hMeet : MeetClosed C)
    {a b : T} (ha : a ∈ C) (hb : b ∈ C)
    (hab : SameComponent a b)
    (hlev : LevelTree.lev (LevelTree.meet a b) = i) :
    RepresentedBefore H F m i :=
  representedBefore_of_node H F m i hC
    (hMeet ha hb hab) hlev

/-- A prefix envelope containing a node above i has a first source level,
strictly before m, whose target image lies above i. -/
theorem exists_first_above_in_prefix
    (H : SMTree S) (F : ShapeMap S) (m i : Nat)
    {C : Set T} (hC : IsPrefixEnvelope F m C)
    {c : T} (hc : c ∈ C) (hic : i < LevelTree.lev c) :
    ∃ n < m,
      i < H.levelMap F n ∧
      ∀ k < n, H.levelMap F k ≤ i := by
  obtain ⟨y, hym, hy⟩ := hC hc
  have hyAbove :
      i < H.levelMap F (LevelTree.lev y) := by
    calc
      i < LevelTree.lev c := hic
      _ = LevelTree.lev (F y) := by rw [hy]
      _ = H.levelMap F (LevelTree.lev y) :=
        (H.levelMap_eq F (a := y)).symm
  let P : Nat → Prop := fun n => i < H.levelMap F n
  have hExists : ∃ n, P n := ⟨LevelTree.lev y, hyAbove⟩
  let n := Nat.find hExists
  have hnP : i < H.levelMap F n := Nat.find_spec hExists
  have hn_le_y : n ≤ LevelTree.lev y := by
    exact Nat.find_min' hExists hyAbove
  have hnm : n < m := lt_of_le_of_lt hn_le_y hym
  refine ⟨n, hnm, hnP, ?_⟩
  intro k hkn
  have hnot : ¬ P k := Nat.find_min hExists hkn
  exact Nat.le_of_not_gt hnot

/-- If i is omitted by the competing prefix, the first target level above i
is separated from all earlier target levels by a genuine gap. -/
theorem exists_gap_of_omitted_prefix_level
    (H : SMTree S) (F : ShapeMap S) (m i : Nat)
    {C : Set T} (hC : IsPrefixEnvelope F m C)
    (homit : ¬ RepresentedBefore H F m i)
    {c : T} (hc : c ∈ C) (hic : i < LevelTree.lev c) :
    ∃ n < m,
      i < H.levelMap F n ∧
      ∀ k < n, H.levelMap F k < i := by
  obtain ⟨n, hnm, hnAbove, hnmin⟩ :=
    exists_first_above_in_prefix H F m i hC hc hic
  refine ⟨n, hnm, hnAbove, ?_⟩
  intro k hkn
  have hle := hnmin k hkn
  by_contra hnot
  have heq : H.levelMap F k = i := by omega
  exact homit ⟨k, lt_trans hkn hnm, heq⟩

/-- If the competing prefix omits i but contains a node above i, then the
crossing map at i extends to an admissible map skipping only i. -/
theorem exists_skip_extension_of_omitted_prefix_level
    (H : SMTree S) (E : MMap H) (m i : Nat)
    {C : Set T} (hC : IsPrefixEnvelope E.map m C)
    (homit : ¬ RepresentedBefore H E.map m i)
    {c : T} (hc : c ∈ C) (hic : i < LevelTree.lev c) :
    ∃ D : MMap H,
      D.map.SkipsOnly i ∧
      ∀ ⦃z : T⦄, z ∈ C → ∀ (hiz : i < LevelTree.lev z),
        D (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz) := by
  obtain ⟨n, _hnm, hnAbove, hnBelow⟩ :=
    exists_gap_of_omitted_prefix_level H E.map m i hC homit hc hic
  apply exists_oneLevel_skip_extension_of_gap H E C i n
  · intro z hz
    exact prefixRange_subset_range E.map m (hC hz)
  · exact hnAbove
  · exact hnBelow

/-- Local trichotomy used in the algorithm. -/
def IsInterestingAt
    (H : SMTree S) (C : Set T) (i : Nat) : Prop :=
  (∃ x ∈ C, LevelTree.lev x = i) ∨
  (∃ a ∈ C, ∃ b ∈ C,
    SameComponent a b ∧ LevelTree.lev (LevelTree.meet a b) = i) ∨
  ¬ ∃ D : MMap H,
      D.map.SkipsOnly i ∧
      ∀ ⦃z : T⦄, z ∈ C → ∀ (hiz : i < LevelTree.lev z),
        D (LevelTree.ancestor z i (Nat.le_of_lt hiz)) =
          LevelTree.ancestor z (i + 1) (Nat.succ_le_iff.mpr hiz)

/-- Every interesting level below the top is forced to occur in any competing
prefix envelope of the current closure. -/
theorem representedBefore_of_interesting
    (H : SMTree S) (E : MMap H) (m i : Nat)
    {C : Set T}
    (hC : IsPrefixEnvelope E.map m C)
    (hMeet : MeetClosed C)
    (hHigh : ∃ c ∈ C, i < LevelTree.lev c)
    (hInteresting : IsInterestingAt H C i) :
    RepresentedBefore H E.map m i := by
  by_contra homit
  rcases hInteresting with hnode | hmeetOrSkip
  · rcases hnode with ⟨x, hxC, hxlev⟩
    exact homit (representedBefore_of_node H E.map m i hC hxC hxlev)
  · rcases hmeetOrSkip with hmeet | hskip
    · rcases hmeet with ⟨a, ha, b, hb, hab, hlev⟩
      exact homit
        (representedBefore_of_meet H E.map m i hC hMeet ha hb hab hlev)
    · obtain ⟨c, hc, hic⟩ := hHigh
      exact hskip
        (exists_skip_extension_of_omitted_prefix_level
          H E m i hC homit hc hic)

end Envelope
end SMTree
end SuccessorTree
