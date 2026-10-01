import SuccessorTree.Approximation
import Mathlib.Tactic

/-!
# Canonical extensions

Formalization of Proposition 1.12 from the successor-tree paper.

The central M2 step removes one missing target level between two consecutive
source levels while preserving the already-fixed source prefix.
-/

namespace SuccessorTree

open LevelTree

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace SMTree

/-- Every shape-preserving self-map of the level set moves level n to at least
n. -/
theorem level_le_levelMap (H : SMTree S) (F : ShapeMap S) :
    ∀ n : Nat, n ≤ H.levelMap F n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hs :=
        H.levelMap_strictMono F (Nat.lt_succ_self n)
      omega

/-- Agreement of global shape maps through source level n gives agreement of
their induced level maps on every lower source level. -/
theorem levelMap_eq_of_agreesThrough
    (H : SMTree S) {F G : ShapeMap S} {n k : Nat}
    (hFG : F.AgreesThrough G n) (hk : k ≤ n) :
    H.levelMap F k = H.levelMap G k := by
  obtain ⟨a, ha⟩ := H.level_nonempty k
  have ha_le : LevelTree.lev a ≤ n := by
    simpa [ha] using hk
  calc
    H.levelMap F k = LevelTree.lev (F a) := by
      simpa [ha] using H.levelMap_eq F (a := a)
    _ = LevelTree.lev (G a) := by
      rw [hFG a ha_le]
    _ = H.levelMap G k := by
      simpa [ha] using (H.levelMap_eq G (a := a)).symm

/-- Any target level strictly between the images of two consecutive source
levels is skipped. -/
theorem skips_between_consecutive
    (H : SMTree S) (F : ShapeMap S) (m t : Nat)
    (hlo : H.levelMap F m < t)
    (hhi : t < H.levelMap F (m + 1)) :
    F.Skips t := by
  intro ht
  have ht' : t ∈ Set.range (H.levelMap F) := by
    rw [H.range_levelMap F]
    exact ht
  rcases ht' with ⟨j, hj⟩
  have hmono := (H.levelMap_strictMono F).monotone
  by_cases hjm : j ≤ m
  · have hle := hmono hjm
    rw [hj] at hle
    omega
  · have hmj : m + 1 ≤ j := by omega
    have hle := hmono hmj
    rw [hj] at hle
    omega

/-- One application of M2 removes the last target gap before level m+1.

The new map agrees with F through source level m and sends source level m+1
one target level lower. -/
theorem lower_next_level_once
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (m : Nat)
    (hgap :
      H.levelMap F m + 1 < H.levelMap F (m + 1)) :
    ∃ F' : ShapeMap S,
      F' ∈ H.M ∧
      F'.AgreesThrough F m ∧
      H.levelMap F' (m + 1) = H.levelMap F (m + 1) - 1 := by
  obtain ⟨a, ha⟩ := H.level_nonempty (m + 1)
  have hFa :
      LevelTree.lev (F a) = H.levelMap F (m + 1) := by
    simpa [ha] using (H.levelMap_eq F (a := a)).symm
  have htarget_lo :
      H.levelMap F m < H.levelMap F (m + 1) - 1 := by
    omega
  have htarget_hi :
      H.levelMap F (m + 1) - 1 < H.levelMap F (m + 1) := by
    omega
  have hskip :
      F.Skips (H.levelMap F (m + 1) - 1) :=
    H.skips_between_consecutive F m
      (H.levelMap F (m + 1) - 1) htarget_lo htarget_hi
  have hFa_pos : 0 < LevelTree.lev (F a) := by
    rw [hFa]
    omega
  have hskip_a :
      F.Skips (LevelTree.lev (F a) - 1) := by
    simpa [hFa] using hskip
  obtain ⟨F1, F2, hF1, hF2, hF2skip, hcomp⟩ :=
    H.m2 (m + 1) F hF a ha hFa_pos hskip_a
  have hF2skip' :
      F2.SkipsOnly (H.levelMap F (m + 1) - 1) := by
    simpa [hFa] using hF2skip

  have hF1agree : F1.AgreesThrough F m := by
    intro x hx
    have hx_mono :
        H.levelMap F (LevelTree.lev x) ≤ H.levelMap F m :=
      (H.levelMap_strictMono F).monotone hx
    have hFx :
        LevelTree.lev (F x) = H.levelMap F (LevelTree.lev x) :=
      (H.levelMap_eq F (a := x)).symm
    have hcomp_x :
        F2 (F1 x) = F x :=
      hcomp x (by omega)
    have hinput_le_output :
        LevelTree.lev (F1 x) ≤ LevelTree.lev (F2 (F1 x)) := by
      calc
        LevelTree.lev (F1 x) ≤ H.levelMap F2 (LevelTree.lev (F1 x)) :=
          H.level_le_levelMap F2 _
        _ = LevelTree.lev (F2 (F1 x)) :=
          H.levelMap_eq F2 (a := F1 x)
    have hF1x_lt :
        LevelTree.lev (F1 x) < H.levelMap F (m + 1) - 1 := by
      rw [hcomp_x] at hinput_le_output
      rw [hFx] at hinput_le_output
      omega
    have hfix :
        F2 (F1 x) = F1 x :=
      H.eq_id_below_skip F2
        (H.levelMap F (m + 1) - 1) hF2skip' hF1x_lt
    exact hfix.symm.trans hcomp_x

  have hF1a :
      H.levelMap F1 (m + 1) = LevelTree.lev (F1 a) := by
    simpa [ha] using H.levelMap_eq F1 (a := a)
  have hlevel_comp :
      H.levelMap F2 (H.levelMap F1 (m + 1)) =
        H.levelMap F (m + 1) := by
    calc
      H.levelMap F2 (H.levelMap F1 (m + 1)) =
          H.levelMap F2 (LevelTree.lev (F1 a)) := by rw [hF1a]
      _ = LevelTree.lev (F2 (F1 a)) :=
          H.levelMap_eq F2 (a := F1 a)
      _ = LevelTree.lev (F a) := by
          rw [hcomp a (by omega)]
      _ = H.levelMap F (m + 1) := hFa

  have hnext :
      H.levelMap F1 (m + 1) =
        H.levelMap F (m + 1) - 1 := by
    rw [H.levelMap_of_skipsOnly F2
      (H.levelMap F (m + 1) - 1) hF2skip'] at hlevel_comp
    by_cases hlt :
        H.levelMap F1 (m + 1) <
          H.levelMap F (m + 1) - 1
    · simp [hlt] at hlevel_comp
      omega
    · simp [Nat.not_lt.mpr (Nat.le_of_not_gt hlt)] at hlevel_comp
      omega

  exact ⟨F1, hF1, hF1agree, hnext⟩

end SMTree

end SuccessorTree
