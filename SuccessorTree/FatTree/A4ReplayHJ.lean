import SuccessorTree.FatTree.A4ReplayWord
import SuccessorTree.HalesJewett.VariableWord

/-!
# Hales--Jewett on replayed saturated profiles

This is the purely finite combinatorial step after profile saturation.  The
alphabet is the finite subtype of profiles already witnessed by the saturated
collector; words are interpreted by `ProfileReplayState.word`.
-/

namespace SuccessorTree
namespace SMTree

universe u v w z

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

namespace ProfileReplayState

/-- The finite alphabet of profiles witnessed by a collector. -/
abbrev SeenProfile
    {c : Nat} {C : Type w} [Fintype C]
    {U : FatTree H} {a : Nat}
    {trace : C → AM H c 1}
    (K : ProfileCollector H U a trace) :=
  {p : FanProfile H C trace // p ∈ K.seen}

noncomputable instance seenProfileFintype
    {c : Nat} {C : Type w} [Fintype C]
    {U : FatTree H} {a : Nat}
    {trace : C → AM H c 1}
    (K : ProfileCollector H U a trace) :
    Fintype (SeenProfile H K) := by
  classical
  exact Fintype.ofFinite _

/-- A nonempty seen finset supplies a nonempty Hales--Jewett alphabet. -/
theorem seenProfile_nonempty
    {c : Nat} {C : Type w} [Fintype C]
    {U : FatTree H} {a : Nat}
    {trace : C → AM H c 1}
    (K : ProfileCollector H U a trace)
    (hseen : K.seen.Nonempty) :
    Nonempty (SeenProfile H K) := by
  rcases hseen with ⟨alpha, halpha⟩
  exact ⟨⟨alpha, halpha⟩⟩

/-- Starred Hales--Jewett for an arbitrary finite colouring of replay-history
states.  The line is a word over the collector's seen-profile alphabet. -/
theorem replayWordStarHJ
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    {κ : Type z} [Fintype κ]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (hseen : K.seen.Nonempty)
    (colour : ProfileReplayState H U a trace hend K → κ) :
    ∃ L : StarLine (SeenProfile H K),
      ∀ alpha : SeenProfile H K,
        colour (word H U a trace hend K (L.eval alpha)) =
          colour (word H U a trace hend K L.star) := by
  classical
  letI : Nonempty (SeenProfile H K) :=
    seenProfile_nonempty H K hseen
  let wordColour : List (SeenProfile H K) → κ :=
    fun w => colour (word H U a trace hend K w)
  obtain ⟨L, hL⟩ :=
    HalesJewett.starHJ_finite
      (α := SeenProfile H K) (κ := κ) wordColour
  exact ⟨L, hL⟩

/-- Coordinatewise version: a finite family of colours can be stabilized
simultaneously on the same replay line. -/
theorem replayWordStarHJ_family
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    {I : Type z} [Fintype I]
    {κ : Type*} [Fintype κ]
    (U : FatTree H) (a : Nat)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (K : ProfileCollector H U a trace)
    (hseen : K.seen.Nonempty)
    (colour :
      ProfileReplayState H U a trace hend K → I → κ) :
    ∃ L : StarLine (SeenProfile H K),
      ∀ alpha : SeenProfile H K, ∀ i : I,
        colour (word H U a trace hend K (L.eval alpha)) i =
          colour (word H U a trace hend K L.star) i := by
  classical
  letI : Fintype (I → κ) := Fintype.ofFinite _
  obtain ⟨L, hL⟩ :=
    replayWordStarHJ H U a trace hend K hseen
      (fun R i => colour R i)
  refine ⟨L, ?_⟩
  intro alpha i
  exact congrFun (hL alpha) i

end ProfileReplayState

end FatTree
end SMTree
end SuccessorTree
