import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# Envelopes: closure operations

This file starts the formalisation of the manuscript section "Envelopes and
embedding types".  It isolates the closure facts used before the envelope
algorithm itself.  Meets are used only inside a root component, represented by
existence of a common predecessor.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Two nodes lie in the same root component iff they have a common
predecessor.  This formulation does not choose a root. -/
def SameComponent (a b : T) : Prop :=
  ∃ r : T, r ≤ a ∧ r ≤ b

/-- Componentwise meet closure, matching the paper's partial meet notation. -/
def MeetClosed (X : Set T) : Prop :=
  ∀ ⦃a b : T⦄, a ∈ X → b ∈ X → SameComponent a b →
    LevelTree.meet a b ∈ X

/-- Closure under the parameter lists of predecessor steps whose base level
belongs to `I`.  The successor representation is quantified rather than
chosen; S2 makes it unique. -/
def ParameterClosedOver (S : STree T Label) (X : Set T) (I : Set Nat) : Prop :=
  ∀ ⦃a : T⦄, a ∈ X → ∀ ⦃i : Nat⦄, i ∈ I → ∀ (hi : i < LevelTree.lev a),
    ∀ ⦃p : List T⦄ ⦃c : Label⦄,
      S.succ
          (LevelTree.ancestor a i (Nat.le_of_lt hi)) p c =
        some (LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hi)) →
      ∀ ⦃x : T⦄, x ∈ p → x ∈ X

/-- The least componentwise-meet- and parameter-closed superset, defined as
an intersection of all closed supersets. -/
def closure (S : STree T Label) (I : Set Nat) (X : Set T) : Set T :=
  {x | ∀ Y : Set T,
    X ⊆ Y → MeetClosed Y → ParameterClosedOver S Y I → x ∈ Y}

@[simp] theorem subset_closure (S : STree T Label) (I : Set Nat) (X : Set T) :
    X ⊆ closure S I X := by
  intro x hx Y hXY _ _
  exact hXY hx

theorem closure_minimal
    (S : STree T Label) (I : Set Nat) (X Y : Set T)
    (hXY : X ⊆ Y) (hmeet : MeetClosed Y)
    (hparam : ParameterClosedOver S Y I) :
    closure S I X ⊆ Y := by
  intro x hx
  exact hx Y hXY hmeet hparam

theorem closure_meetClosed
    (S : STree T Label) (I : Set Nat) (X : Set T) :
    MeetClosed (closure S I X) := by
  intro a b ha hb hab
  intro Y hXY hmeet hparam
  exact hmeet (ha Y hXY hmeet hparam) (hb Y hXY hmeet hparam) hab

theorem closure_parameterClosed
    (S : STree T Label) (I : Set Nat) (X : Set T) :
    ParameterClosedOver S (closure S I X) I := by
  intro a ha i hi hia p c hsucc x hx
  intro Y hXY hmeet hparam
  exact hparam (ha Y hXY hmeet hparam) hi hia hsucc hx

/-- A shape map cannot merge root components. -/
theorem sameComponent_of_map_sameComponent
    (F : ShapeMap S) {a b : T}
    (h : SameComponent (F a) (F b)) :
    SameComponent a b := by
  rcases h with ⟨c, hca, hcb⟩
  let ra := LevelTree.ancestor a 0 (Nat.zero_le _)
  let rb := LevelTree.ancestor b 0 (Nat.zero_le _)
  let r := LevelTree.ancestor c 0 (Nat.zero_le _)
  have hra_a : ra ≤ a := LevelTree.ancestor_le a 0 (Nat.zero_le _)
  have hrb_b : rb ≤ b := LevelTree.ancestor_le b 0 (Nat.zero_le _)
  have hr_c : r ≤ c := LevelTree.ancestor_le c 0 (Nat.zero_le _)
  have hra0 : LevelTree.lev ra = 0 := LevelTree.level_ancestor a 0 (Nat.zero_le _)
  have hrb0 : LevelTree.lev rb = 0 := LevelTree.level_ancestor b 0 (Nat.zero_le _)
  have hr0 : LevelTree.lev r = 0 := LevelTree.level_ancestor c 0 (Nat.zero_le _)
  have hra_Fa : ra ≤ F a := by
    exact (F.root_le' hra0).trans (F.map_le_of_le hra_a)
  have hrb_Fb : rb ≤ F b := by
    exact (F.root_le' hrb0).trans (F.map_le_of_le hrb_b)
  have hr_Fa : r ≤ F a := hr_c.trans hca
  have hr_Fb : r ≤ F b := hr_c.trans hcb
  have hrar : ra = r := by
    rcases LevelTree.comparable_below hra_Fa hr_Fa with hle | hle
    · exact LevelTree.same_level_of_le hle (hra0.trans hr0.symm)
    · exact (LevelTree.same_level_of_le hle (hr0.trans hra0.symm)).symm
  have hrbr : rb = r := by
    rcases LevelTree.comparable_below hrb_Fb hr_Fb with hle | hle
    · exact LevelTree.same_level_of_le hle (hrb0.trans hr0.symm)
    · exact (LevelTree.same_level_of_le hle (hr0.trans hrb0.symm)).symm
  refine ⟨ra, hra_a, ?_⟩
  rw [hrar, ← hrbr]
  exact hrb_b

/-- The range of every shape-preserving map is componentwise meet-closed. -/
theorem range_meetClosed (F : ShapeMap S) :
    MeetClosed (Set.range F) := by
  intro a b ha hb hab
  rcases ha with ⟨a0, rfl⟩
  rcases hb with ⟨b0, rfl⟩
  have hsource : SameComponent a0 b0 :=
    sameComponent_of_map_sameComponent F hab
  refine ⟨LevelTree.meet a0 b0, ?_⟩
  exact F.map_meet hsource

/-- If a target level is in the range of a shape map, then all parameters of
an image node at the next target step are themselves in the image. -/
theorem range_parameterClosed
    (H : SMTree S) (F : ShapeMap S) :
    ParameterClosedOver S (Set.range F) F.levelRange := by
  intro a ha i hi hia p c htarget z hz
  rcases ha with ⟨x, rfl⟩
  rcases hi with ⟨u, hu⟩
  let j : Nat := LevelTree.lev u
  have hmapj : H.levelMap F j = i := by
    dsimp [j]
    exact (H.levelMap_eq F (a := u)).trans hu
  have hmapx : H.levelMap F (LevelTree.lev x) = LevelTree.lev (F x) :=
    H.levelMap_eq F (a := x)
  have hjx : j < LevelTree.lev x := by
    by_contra hnot
    have hxj : LevelTree.lev x ≤ j := Nat.le_of_not_gt hnot
    have hmono := (H.levelMap_strictMono F).monotone hxj
    rw [hmapx, hmapj] at hmono
    omega
  have hjle : j ≤ LevelTree.lev x := Nat.le_of_lt hjx
  have hj1le : j + 1 ≤ LevelTree.lev x := Nat.succ_le_iff.mpr hjx
  let x0 := LevelTree.ancestor x j hjle
  let x1 := LevelTree.ancestor x (j + 1) hj1le
  have hx0x : x0 ≤ x := LevelTree.ancestor_le x j hjle
  have hx1x : x1 ≤ x := LevelTree.ancestor_le x (j + 1) hj1le
  have hx0lev : LevelTree.lev x0 = j := LevelTree.level_ancestor x j hjle
  have hx1lev : LevelTree.lev x1 = j + 1 :=
    LevelTree.level_ancestor x (j + 1) hj1le
  have hx0x1 : x0 ≤ x1 := by
    rcases LevelTree.comparable_below hx0x hx1x with h | h
    · exact h
    · have hlev := LevelTree.level_le_of_le h
      omega
  have hx0cov : x0 ⋖ x1 := by
    apply LevelTree.covBy_of_le_level_succ hx0x1
    omega
  obtain ⟨q, d, hsource⟩ := S.s3 hx0cov
  obtain ⟨y, hy, hyx1⟩ := F.weak_succ' hsource
  have hyx : y ≤ F x := hyx1.trans (F.map_le_of_le hx1x)
  have hFx0x : F x0 ≤ F x := F.map_le_of_le hx0x
  have hFx0lev : LevelTree.lev (F x0) = i := by
    have hsame : LevelTree.lev (F x0) = LevelTree.lev (F u) := by
      apply F.level_eq_of_level_eq
      dsimp [j] at hx0lev
      exact hx0lev
    exact hsame.trans hu
  have hFx0 :
      F x0 = LevelTree.ancestor (F x) i (Nat.le_of_lt hia) :=
    LevelTree.eq_ancestor_of_le hFx0x hFx0lev (Nat.le_of_lt hia)
  have hylev : LevelTree.lev y = i + 1 := by
    have hcov := S.covBy_of_succ_eq_some hy
    rw [LevelTree.covBy_level_eq hcov, hFx0lev]
  have hyEq :
      y = LevelTree.ancestor (F x) (i + 1) (Nat.succ_le_iff.mpr hia) :=
    LevelTree.eq_ancestor_of_le hyx hylev (Nat.succ_le_iff.mpr hia)
  have hgenerated :
      S.succ
          (LevelTree.ancestor (F x) i (Nat.le_of_lt hia))
          (q.map F) d =
        some (LevelTree.ancestor (F x) (i + 1) (Nat.succ_le_iff.mpr hia)) := by
    simpa [hFx0, hyEq] using hy
  have hpq : p = q.map F := (S.s2 htarget hgenerated).2.1
  rw [hpq] at hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  exact ⟨w, rfl⟩

/-- Restrict parameter closure from a set of levels to a subset. -/
theorem ParameterClosedOver.mono_levels
    {X : Set T} {I J : Set Nat}
    (h : ParameterClosedOver S X J) (hIJ : I ⊆ J) :
    ParameterClosedOver S X I := by
  intro a ha i hi hia p c hs x hx
  exact h ha (hIJ hi) hia hs hx

/-- The manuscript's closure observation: an envelope of `X` also envelopes
its componentwise meet/parameter closure over target levels met by the map. -/
theorem closure_subset_range
    (H : SMTree S) (F : ShapeMap S)
    {X : Set T} {I : Set Nat}
    (hX : X ⊆ Set.range F) (hI : I ⊆ F.levelRange) :
    closure S I X ⊆ Set.range F := by
  apply closure_minimal S I X (Set.range F) hX
  · exact range_meetClosed F
  · exact (range_parameterClosed H F).mono_levels hI

/-- `F` is an envelope of `X` precisely when `X` is contained in its range. -/
def IsEnvelope (F : ShapeMap S) (X : Set T) : Prop :=
  X ⊆ Set.range F

/-- The canonical embedding type associated with an envelope. -/
def embeddingType (F : ShapeMap S) (X : Set T) : Set T :=
  F ⁻¹' X

theorem envelope_closure
    (H : SMTree S) (F : ShapeMap S)
    {X : Set T} {I : Set Nat}
    (hF : IsEnvelope F X) (hI : I ⊆ F.levelRange) :
    IsEnvelope F (closure S I X) :=
  closure_subset_range H F hF hI

end Envelope
end SMTree
end SuccessorTree
