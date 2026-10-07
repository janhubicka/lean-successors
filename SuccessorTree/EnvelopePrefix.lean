import SuccessorTree.Envelope
import SuccessorTree.Approximation
import Mathlib.Tactic

/-!
# Finite-prefix envelopes

The manuscript defines envelopes using both total maps in M and finite
approximations in AM.  Minimality therefore needs the closure observation with
control of the source prefix, not merely containment in the range of a total
extension.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Image of the source levels strictly below m. -/
def prefixRange (F : ShapeMap S) (m : Nat) : Set T :=
  {x | ∃ y : T, LevelTree.lev y < m ∧ F y = x}

/-- A total representative envelopes X already inside its first m source
levels. This is the total-map form of a finite envelope of height at most m. -/
def IsPrefixEnvelope (F : ShapeMap S) (m : Nat) (X : Set T) : Prop :=
  X ⊆ prefixRange F m

theorem prefixRange_subset_range (F : ShapeMap S) (m : Nat) :
    prefixRange F m ⊆ Set.range F := by
  rintro x ⟨y, _, rfl⟩
  exact ⟨y, rfl⟩

/-- The prefix range is componentwise meet-closed. -/
theorem prefixRange_meetClosed (F : ShapeMap S) (m : Nat) :
    MeetClosed (prefixRange F m) := by
  intro a b ha hb hab
  rcases ha with ⟨a0, ha0m, rfl⟩
  rcases hb with ⟨b0, hb0m, rfl⟩
  have hsource : SameComponent a0 b0 :=
    sameComponent_of_map_sameComponent F hab
  refine ⟨LevelTree.meet a0 b0, ?_, F.map_meet hsource⟩
  have hmeet : LevelTree.meet a0 b0 ≤ a0 :=
    LevelTree.meet_le_left hsource
  have hlev := LevelTree.level_le_of_le hmeet
  omega

/-- The prefix range is parameter-closed over target levels represented by
source levels inside the same prefix. -/
theorem prefixRange_parameterClosed
    (H : SMTree S) (F : ShapeMap S) (m : Nat) :
    ParameterClosedOver S (prefixRange F m)
      {i | ∃ j < m, H.levelMap F j = i} := by
  intro a ha i hi hia p c htarget z hz
  rcases ha with ⟨x, hxm, rfl⟩
  rcases hi with ⟨j, hjm, hji⟩
  have hmapx : H.levelMap F (LevelTree.lev x) = LevelTree.lev (F x) :=
    H.levelMap_eq F (a := x)
  have hjx : j < LevelTree.lev x := by
    by_contra hnot
    have hxj : LevelTree.lev x ≤ j := Nat.le_of_not_gt hnot
    have hmono := (H.levelMap_strictMono F).monotone hxj
    rw [hmapx, hji] at hmono
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
    calc
      LevelTree.lev (F x0) = H.levelMap F j := by
        rw [← hx0lev]
        exact (H.levelMap_eq F (a := x0)).symm
      _ = i := hji
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
  refine ⟨w, ?_, rfl⟩
  have hwlt := S.parameter_level_lt hsource hw
  rw [hx0lev] at hwlt
  omega

/-- Finite-prefix form of Observation 5.7. -/
theorem prefixEnvelope_closure
    (H : SMTree S) (F : ShapeMap S) (m : Nat)
    {X : Set T} {I : Set Nat}
    (hF : IsPrefixEnvelope F m X)
    (hI : I ⊆ {i | ∃ j < m, H.levelMap F j = i}) :
    IsPrefixEnvelope F m (closure S I X) := by
  apply closure_minimal S I X (prefixRange F m) hF
  · exact prefixRange_meetClosed F m
  · exact
      (prefixRange_parameterClosed H F m).mono_levels hI

/-- Every finite envelope has a total representative which is a prefix
envelope of the same height.  This wrapper is intentionally stated using a
realized restricted map, so it also applies directly to AM representatives. -/
theorem prefixEnvelope_of_restricted
    (H : SMTree S) (F : MMap H) (m : Nat) (X : Set T)
    (h :
      ∀ x ∈ X, ∃ y : T,
        LevelTree.lev y < m ∧ F y = x) :
    IsPrefixEnvelope F.map m X := by
  exact h

end Envelope
end SMTree
end SuccessorTree
