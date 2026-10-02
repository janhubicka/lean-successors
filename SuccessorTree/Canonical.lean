import SuccessorTree.Approximation
import Mathlib.Tactic

/-!
# Canonical extensions of finite successor-tree approximations

This file begins the formalization of Proposition 1.12 / Proposition 2.2
from the successor-tree manuscript.  The first lemma is the finite M2
operation used by the manuscript: close one target-level gap while preserving
all previously frozen input levels.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A genuine gap before input level m+1 means that the last target level
below F(m+1) is omitted from the range of F. -/
theorem skips_pred_of_level_gap
    (H : SMTree S) (F : MMap H) (m : Nat)
    (hgap :
      H.levelMap F.map m + 1 <
        H.levelMap F.map (m + 1)) :
    F.map.Skips (H.levelMap F.map (m + 1) - 1) := by
  intro hmem
  rcases hmem with ⟨x, hx⟩
  have hxmap :
      H.levelMap F.map (LevelTree.lev x) =
        H.levelMap F.map (m + 1) - 1 := by
    exact (H.levelMap_eq F.map (a := x)).trans hx
  by_cases hxm : LevelTree.lev x ≤ m
  · have hmono :
        H.levelMap F.map (LevelTree.lev x) ≤
          H.levelMap F.map m :=
      (H.levelMap_strictMono F.map).monotone hxm
    omega
  · have hmx : m + 1 ≤ LevelTree.lev x := by omega
    have hmono :
        H.levelMap F.map (m + 1) ≤
          H.levelMap F.map (LevelTree.lev x) :=
      (H.levelMap_strictMono F.map).monotone hmx
    omega

/-- One application of M2 closes one unit of a gap.  The new map agrees with
F through input level m and sends level m+1 exactly one target level lower. -/
theorem exists_lower_gap_once
    (H : SMTree S) (F : MMap H) (m : Nat)
    (hgap :
      H.levelMap F.map m + 1 <
        H.levelMap F.map (m + 1)) :
    ∃ F' : MMap H,
      (∀ x : T, LevelTree.lev x ≤ m → F' x = F x) ∧
      H.levelMap F'.map (m + 1) =
        H.levelMap F.map (m + 1) - 1 := by
  obtain ⟨a, ha⟩ := H.level_nonempty (m + 1)
  have hFa :
      LevelTree.lev (F a) =
        H.levelMap F.map (m + 1) := by
    have h := H.levelMap_eq F.map (a := a)
    simpa [ha] using h.symm
  have hpos : 0 < LevelTree.lev (F a) := by
    have hstrict :=
      H.levelMap_strictMono F.map (Nat.zero_lt_succ m)
    have hnonneg : 0 ≤ H.levelMap F.map 0 := Nat.zero_le _
    rw [hFa]
    omega
  have hskip :
      F.map.Skips (LevelTree.lev (F a) - 1) := by
    rw [hFa]
    exact H.skips_pred_of_level_gap F m hgap
  obtain ⟨F1, F2, hF1, hF2, hF2skip, hagree⟩ :=
    H.m2 (m + 1) F.map F.mem a ha hpos hskip
  let F' : MMap H := ⟨F1, hF1⟩
  refine ⟨F', ?_, ?_⟩
  · intro x hx
    have hcomp : F2 (F1 x) = F x :=
      hagree x (Nat.le_trans hx (Nat.le_succ m))
    have hFxLev :
        LevelTree.lev (F x) ≤ H.levelMap F.map m := by
      calc
        LevelTree.lev (F x) =
            H.levelMap F.map (LevelTree.lev x) :=
          (H.levelMap_eq F.map (a := x)).symm
        _ ≤ H.levelMap F.map m :=
          (H.levelMap_strictMono F.map).monotone hx
    have ht :
        H.levelMap F.map m <
          LevelTree.lev (F a) - 1 := by
      rw [hFa]
      omega
    have hF1lt :
        LevelTree.lev (F1 x) <
          LevelTree.lev (F a) - 1 := by
      by_contra hnot
      have hge :
          LevelTree.lev (F a) - 1 ≤ LevelTree.lev (F1 x) :=
        Nat.le_of_not_gt hnot
      have hlevF2 :
          LevelTree.lev (F2 (F1 x)) =
            LevelTree.lev (F1 x) + 1 := by
        calc
          LevelTree.lev (F2 (F1 x)) =
              H.levelMap F2 (LevelTree.lev (F1 x)) :=
            (H.levelMap_eq F2 (a := F1 x)).symm
          _ = LevelTree.lev (F1 x) + 1 := by
            rw [H.levelMap_of_skipsOnly F2
              (LevelTree.lev (F a) - 1) hF2skip]
            simp [Nat.not_lt.mpr hge]
      rw [hcomp] at hlevF2
      omega
    have hfix :
        F2 (F1 x) = F1 x :=
      H.eq_id_below_skip F2
        (LevelTree.lev (F a) - 1) hF2skip hF1lt
    exact hfix.symm.trans hcomp
  · have hcomp : F2 (F1 a) = F a :=
      hagree a (Nat.le_of_eq ha)
    have hFa1 :
        LevelTree.lev (F1 a) =
          H.levelMap F'.map (m + 1) := by
      have h := H.levelMap_eq F1 (a := a)
      simpa [F', ha] using h.symm
    have htarget :
        LevelTree.lev (F1 a) =
          LevelTree.lev (F a) - 1 := by
      have hlev :
          LevelTree.lev (F2 (F1 a)) =
            if LevelTree.lev (F1 a) <
                  LevelTree.lev (F a) - 1
            then LevelTree.lev (F1 a)
            else LevelTree.lev (F1 a) + 1 := by
        calc
          LevelTree.lev (F2 (F1 a)) =
              H.levelMap F2 (LevelTree.lev (F1 a)) :=
            (H.levelMap_eq F2 (a := F1 a)).symm
          _ = _ :=
            H.levelMap_of_skipsOnly F2
              (LevelTree.lev (F a) - 1) hF2skip _
      rw [hcomp] at hlev
      split at hlev <;> omega
    calc
      H.levelMap F'.map (m + 1) = LevelTree.lev (F1 a) := hFa1.symm
      _ = LevelTree.lev (F a) - 1 := htarget
      _ = H.levelMap F.map (m + 1) - 1 := by rw [hFa]


/-- An M-map fixes every node strictly below a cut level. -/
def MMap.FixesBelow (H : SMTree S) (F : MMap H) (d : Nat) : Prop :=
  ∀ x : T, LevelTree.lev x < d → F x = x

@[simp] theorem MMap.id_fixesBelow
    (H : SMTree S) (d : Nat) :
    (MMap.id H).FixesBelow H d := by
  intro x hx
  rfl

theorem MMap.comp_fixesBelow
    (H : SMTree S) (F G : MMap H) (d : Nat)
    (hF : F.FixesBelow H d)
    (hG : G.FixesBelow H d) :
    (MMap.comp H F G).FixesBelow H d := by
  intro x hx
  rw [MMap.comp_apply, hG x hx, hF x hx]

/-- The factorized form of one M2 gap-lowering step. -/
theorem exists_lower_gap_once_factor
    (H : SMTree S) (F : MMap H) (m : Nat)
    (hgap :
      H.levelMap F.map m + 1 <
        H.levelMap F.map (m + 1)) :
    ∃ G D : MMap H,
      (∀ x : T, LevelTree.lev x ≤ m → G x = F x) ∧
      D.map.SkipsOnly (H.levelMap F.map (m + 1) - 1) ∧
      (∀ x : T, LevelTree.lev x ≤ m + 1 →
        D (G x) = F x) ∧
      H.levelMap G.map (m + 1) =
        H.levelMap F.map (m + 1) - 1 := by
  obtain ⟨a, ha⟩ := H.level_nonempty (m + 1)
  have hFa :
      LevelTree.lev (F a) =
        H.levelMap F.map (m + 1) := by
    have h := H.levelMap_eq F.map (a := a)
    simpa [ha] using h.symm
  have hpos : 0 < LevelTree.lev (F a) := by
    have hstrict :=
      H.levelMap_strictMono F.map (Nat.zero_lt_succ m)
    rw [hFa]
    omega
  have hskip :
      F.map.Skips (LevelTree.lev (F a) - 1) := by
    rw [hFa]
    exact H.skips_pred_of_level_gap F m hgap
  obtain ⟨F1, F2, hF1, hF2, hF2skip, hagree⟩ :=
    H.m2 (m + 1) F.map F.mem a ha hpos hskip
  let G : MMap H := ⟨F1, hF1⟩
  let D : MMap H := ⟨F2, hF2⟩
  have hGagree :
      ∀ x : T, LevelTree.lev x ≤ m → G x = F x := by
    intro x hx
    have hcomp : F2 (F1 x) = F x :=
      hagree x (by omega)
    have hFxLev :
        LevelTree.lev (F x) ≤ H.levelMap F.map m := by
      calc
        LevelTree.lev (F x) =
            H.levelMap F.map (LevelTree.lev x) :=
          (H.levelMap_eq F.map (a := x)).symm
        _ ≤ H.levelMap F.map m :=
          (H.levelMap_strictMono F.map).monotone hx
    have ht :
        H.levelMap F.map m <
          LevelTree.lev (F a) - 1 := by
      rw [hFa]
      omega
    have hF1lt :
        LevelTree.lev (F1 x) <
          LevelTree.lev (F a) - 1 := by
      by_contra hnot
      have hge :
          LevelTree.lev (F a) - 1 ≤ LevelTree.lev (F1 x) := by
        omega
      have hlevF2 :
          LevelTree.lev (F2 (F1 x)) =
            LevelTree.lev (F1 x) + 1 := by
        calc
          LevelTree.lev (F2 (F1 x)) =
              H.levelMap F2 (LevelTree.lev (F1 x)) :=
            (H.levelMap_eq F2 (a := F1 x)).symm
          _ = LevelTree.lev (F1 x) + 1 := by
            rw [H.levelMap_of_skipsOnly F2
              (LevelTree.lev (F a) - 1) hF2skip]
            simp [Nat.not_lt.mpr hge]
      rw [hcomp] at hlevF2
      omega
    have hfix :
        F2 (F1 x) = F1 x :=
      H.eq_id_below_skip F2
        (LevelTree.lev (F a) - 1) hF2skip hF1lt
    exact hfix.symm.trans hcomp
  have hGnext :
      H.levelMap G.map (m + 1) =
        H.levelMap F.map (m + 1) - 1 := by
    have hcomp : F2 (F1 a) = F a :=
      hagree a (by omega)
    have hFa1 :
        LevelTree.lev (F1 a) =
          H.levelMap G.map (m + 1) := by
      have h := H.levelMap_eq F1 (a := a)
      simpa [G, ha] using h.symm
    have htarget :
        LevelTree.lev (F1 a) =
          LevelTree.lev (F a) - 1 := by
      have hlev :
          LevelTree.lev (F2 (F1 a)) =
            if LevelTree.lev (F1 a) <
                  LevelTree.lev (F a) - 1
            then LevelTree.lev (F1 a)
            else LevelTree.lev (F1 a) + 1 := by
        calc
          LevelTree.lev (F2 (F1 a)) =
              H.levelMap F2 (LevelTree.lev (F1 a)) :=
            (H.levelMap_eq F2 (a := F1 a)).symm
          _ = _ :=
            H.levelMap_of_skipsOnly F2
              (LevelTree.lev (F a) - 1) hF2skip _
      rw [hcomp] at hlev
      split at hlev <;> omega
    calc
      H.levelMap G.map (m + 1) = LevelTree.lev (F1 a) := hFa1.symm
      _ = LevelTree.lev (F a) - 1 := htarget
      _ = H.levelMap F.map (m + 1) - 1 := by rw [hFa]
  refine ⟨G, D, hGagree, ?_, ?_, hGnext⟩
  · simpa [D, hFa] using hF2skip
  · intro x hx
    exact hagree x hx

/-- Shape splitting at the first possible target level after the frozen
prefix.  The outer factor fixes all levels below the new cut. -/
theorem exists_close_gap_factor
    (H : SMTree S) (F : MMap H) (m : Nat) :
    ∃ P Q : MMap H,
      (∀ x : T, LevelTree.lev x ≤ m → P x = F x) ∧
      Q.FixesBelow H (H.levelMap F.map m + 1) ∧
      (∀ x : T, LevelTree.lev x ≤ m + 1 →
        Q (P x) = F x) ∧
      H.levelMap P.map (m + 1) =
        H.levelMap F.map m + 1 := by
  generalize hN : H.levelMap F.map (m + 1) = N
  induction N using Nat.strong_induction_on generalizing F with
  | h N ih =>
      have hmono :
          H.levelMap F.map m <
            H.levelMap F.map (m + 1) :=
        H.levelMap_strictMono F.map (Nat.lt_succ_self m)
      by_cases heq :
          H.levelMap F.map (m + 1) =
            H.levelMap F.map m + 1
      · refine ⟨F, MMap.id H, ?_, ?_, ?_, heq⟩
        · intro x hx
          rfl
        · exact MMap.id_fixesBelow H _
        · intro x hx
          rfl
      · have hgap :
            H.levelMap F.map m + 1 <
              H.levelMap F.map (m + 1) := by
          omega
        obtain ⟨G, D, hGagree, hDskip, hDG, hGnext⟩ :=
          H.exists_lower_gap_once_factor F m hgap
        have hGm :
            H.levelMap G.map m =
              H.levelMap F.map m := by
          obtain ⟨x, hx⟩ := H.level_nonempty m
          calc
            H.levelMap G.map m = LevelTree.lev (G x) := by
              simpa [hx] using H.levelMap_eq G.map (a := x)
            _ = LevelTree.lev (F x) := by
              rw [hGagree x (by omega)]
            _ = H.levelMap F.map m := by
              simpa [hx] using (H.levelMap_eq F.map (a := x)).symm
        have hlt :
            H.levelMap G.map (m + 1) < N := by
          rw [hGnext, hN]
          omega
        obtain ⟨P, Q, hPagree, hQfix, hQP, hPnext⟩ :=
          ih (H.levelMap G.map (m + 1)) hlt G rfl
        let R : MMap H := MMap.comp H D Q
        refine ⟨P, R, ?_, ?_, ?_, ?_⟩
        · intro x hx
          exact (hPagree x hx).trans (hGagree x hx)
        · intro x hx
          have hQx : Q x = x := hQfix x (by
            simpa only [hGm] using hx)
          have hcut :
              H.levelMap F.map m + 1 ≤
                H.levelMap F.map (m + 1) - 1 := by
            omega
          have hDx : D x = x := by
            apply H.eq_id_below_skip D.map
              (H.levelMap F.map (m + 1) - 1) hDskip
            exact lt_of_lt_of_le hx hcut
          change D (Q x) = x
          rw [hQx, hDx]
        · intro x hx
          change D (Q (P x)) = F x
          rw [hQP x hx]
          exact hDG x hx
        · calc
            H.levelMap P.map (m + 1) =
                H.levelMap G.map m + 1 := hPnext
            _ = H.levelMap F.map m + 1 := by rw [hGm]

/-- Repeatedly apply the one-step M2 operation until the gap after level m
is completely closed. -/
theorem exists_close_gap
    (H : SMTree S) (F : MMap H) (m : Nat) :
    ∃ F' : MMap H,
      (∀ x : T, LevelTree.lev x ≤ m → F' x = F x) ∧
      H.levelMap F'.map (m + 1) =
        H.levelMap F.map m + 1 := by
  generalize hN : H.levelMap F.map (m + 1) = N
  induction N using Nat.strong_induction_on generalizing F with
  | h N ih =>
      have hmono :
          H.levelMap F.map m <
            H.levelMap F.map (m + 1) :=
        H.levelMap_strictMono F.map (Nat.lt_succ_self m)
      by_cases heq :
          H.levelMap F.map (m + 1) =
            H.levelMap F.map m + 1
      · refine ⟨F, ?_, heq⟩
        intro x hx
        rfl
      · have hgap :
            H.levelMap F.map m + 1 <
              H.levelMap F.map (m + 1) := by
          omega
        obtain ⟨G, hGagree, hGnext⟩ :=
          H.exists_lower_gap_once F m hgap
        have hGm :
            H.levelMap G.map m =
              H.levelMap F.map m := by
          obtain ⟨x, hx⟩ := H.level_nonempty m
          calc
            H.levelMap G.map m = LevelTree.lev (G x) := by
              simpa [hx] using H.levelMap_eq G.map (a := x)
            _ = LevelTree.lev (F x) := by
              rw [hGagree x (by omega)]
            _ = H.levelMap F.map m := by
              simpa [hx] using (H.levelMap_eq F.map (a := x)).symm
        have hlt :
            H.levelMap G.map (m + 1) < N := by
          rw [hGnext, hN]
          omega
        obtain ⟨K, hKagree, hKnext⟩ :=
          ih (H.levelMap G.map (m + 1)) hlt G rfl
        refine ⟨K, ?_, ?_⟩
        · intro x hx
          exact (hKagree x hx).trans (hGagree x hx)
        · calc
            H.levelMap K.map (m + 1) =
                H.levelMap G.map m + 1 := hKnext
            _ = H.levelMap F.map m + 1 := by rw [hGm]

/-- A chosen gap-closing refinement. -/
noncomputable def closeGap
    (H : SMTree S) (F : MMap H) (m : Nat) : MMap H :=
  Classical.choose (H.exists_close_gap F m)

theorem closeGap_agrees
    (H : SMTree S) (F : MMap H) (m : Nat)
    (x : T) (hx : LevelTree.lev x ≤ m) :
    H.closeGap F m x = F x :=
  (Classical.choose_spec (H.exists_close_gap F m)).1 x hx

theorem closeGap_level_succ
    (H : SMTree S) (F : MMap H) (m : Nat) :
    H.levelMap (H.closeGap F m).map (m + 1) =
      H.levelMap F.map m + 1 :=
  (Classical.choose_spec (H.exists_close_gap F m)).2

/-- Stages of the canonical-extension fusion.  Before level n the original
map is unchanged; thereafter stage i+1 closes exactly the gap after i. -/
noncomputable def canonicalStage
    (H : SMTree S) (F : MMap H) (n : Nat) : Nat → MMap H
  | 0 => F
  | i + 1 =>
      if n ≤ i then
        H.closeGap (H.canonicalStage F n i) i
      else
        H.canonicalStage F n i

theorem canonicalStage_succ_agrees
    (H : SMTree S) (F : MMap H) (n i : Nat)
    (x : T) (hx : LevelTree.lev x ≤ i) :
    H.canonicalStage F n (i + 1) x =
      H.canonicalStage F n i x := by
  rw [canonicalStage]
  by_cases hni : n ≤ i
  · simp only [hni, if_true]
    exact H.closeGap_agrees (H.canonicalStage F n i) i x hx
  · simp only [hni, if_false]

theorem canonicalStage_eq_initial_of_le
    (H : SMTree S) (F : MMap H) (n : Nat) :
    ∀ i : Nat, i ≤ n → H.canonicalStage F n i = F := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
      have hnot : ¬ n ≤ i := by omega
      rw [canonicalStage]
      simp only [hnot, if_false]
      exact ih (by omega)

theorem canonicalStage_level_succ
    (H : SMTree S) (F : MMap H) (n i : Nat)
    (hni : n ≤ i) :
    H.levelMap (H.canonicalStage F n (i + 1)).map (i + 1) =
      H.levelMap (H.canonicalStage F n i).map i + 1 := by
  rw [canonicalStage]
  simp only [hni, if_true]
  exact H.closeGap_level_succ (H.canonicalStage F n i) i

theorem canonicalStage_fusionStable
    (H : SMTree S) (F : MMap H) (n : Nat) :
    ShapeMap.FusionStable
      (fun i => (H.canonicalStage F n i).map) := by
  intro i x hx
  exact (H.canonicalStage_succ_agrees F n i x hx).symm

/-- Canonical extension of the restriction of F through input level n. -/
noncomputable def canonicalExtension
    (H : SMTree S) (F : MMap H) (n : Nat) : MMap H where
  map :=
    ShapeMap.fusionLimit
      (fun i => (H.canonicalStage F n i).map)
      (H.canonicalStage_fusionStable F n)
  mem :=
    H.fusion_mem
      (fun i => (H.canonicalStage F n i).map)
      (fun i => (H.canonicalStage F n i).mem)
      (H.canonicalStage_fusionStable F n)

theorem canonicalExtension_apply
    (H : SMTree S) (F : MMap H) (n : Nat) (x : T) :
    H.canonicalExtension F n x =
      H.canonicalStage F n (LevelTree.lev x) x := rfl

/-- The canonical extension really extends the prescribed finite prefix. -/
theorem canonicalExtension_agrees
    (H : SMTree S) (F : MMap H) (n : Nat)
    (x : T) (hx : LevelTree.lev x ≤ n) :
    H.canonicalExtension F n x = F x := by
  rw [H.canonicalExtension_apply F n x]
  rw [H.canonicalStage_eq_initial_of_le F n
    (LevelTree.lev x) hx]

/-- The level map of the fusion limit at i is already visible at stage i. -/
theorem canonicalExtension_levelMap_eq_stage
    (H : SMTree S) (F : MMap H) (n i : Nat) :
    H.levelMap (H.canonicalExtension F n).map i =
      H.levelMap (H.canonicalStage F n i).map i := by
  obtain ⟨x, hx⟩ := H.level_nonempty i
  calc
    H.levelMap (H.canonicalExtension F n).map i =
        LevelTree.lev (H.canonicalExtension F n x) := by
      simpa [hx] using
        H.levelMap_eq (H.canonicalExtension F n).map (a := x)
    _ = LevelTree.lev (H.canonicalStage F n i x) := by
      rw [H.canonicalExtension_apply F n x, hx]
    _ = H.levelMap (H.canonicalStage F n i).map i := by
      simpa [hx] using
        (H.levelMap_eq (H.canonicalStage F n i).map
          (a := x)).symm

/-- From the end of the prescribed prefix onward, canonical-extension image
levels are consecutive. -/
theorem canonicalExtension_level_succ
    (H : SMTree S) (F : MMap H) (n i : Nat)
    (hni : n ≤ i) :
    H.levelMap (H.canonicalExtension F n).map (i + 1) =
      H.levelMap (H.canonicalExtension F n).map i + 1 := by
  rw [H.canonicalExtension_levelMap_eq_stage F n (i + 1)]
  rw [H.canonicalExtension_levelMap_eq_stage F n i]
  exact H.canonicalStage_level_succ F n i hni

theorem canonicalExtension_level_at_prefix
    (H : SMTree S) (F : MMap H) (n : Nat) :
    H.levelMap (H.canonicalExtension F n).map n =
      H.levelMap F.map n := by
  rw [H.canonicalExtension_levelMap_eq_stage F n n]
  rw [H.canonicalStage_eq_initial_of_le F n n le_rfl]

/-- Explicit affine formula for every tail image level. -/
theorem canonicalExtension_level_tail
    (H : SMTree S) (F : MMap H) (n : Nat) :
    ∀ k : Nat,
      H.levelMap (H.canonicalExtension F n).map (n + k) =
        H.levelMap F.map n + k := by
  intro k
  induction k with
  | zero =>
      simpa using H.canonicalExtension_level_at_prefix F n
  | succ k ih =>
      calc
        H.levelMap (H.canonicalExtension F n).map (n + (k + 1)) =
            H.levelMap (H.canonicalExtension F n).map
              ((n + k) + 1) := by congr 1 <;> omega
        _ = H.levelMap (H.canonicalExtension F n).map (n + k) + 1 :=
          H.canonicalExtension_level_succ F n (n + k) (by omega)
        _ = H.levelMap F.map n + (k + 1) := by
          rw [ih]
          omega

/-- Every target level at or above the last prescribed image level occurs in
the canonical extension. -/
theorem canonicalExtension_tail_mem_levelRange
    (H : SMTree S) (F : MMap H) (n ell : Nat)
    (hell : H.levelMap F.map n ≤ ell) :
    ell ∈ (H.canonicalExtension F n).map.levelRange := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hell
  have hlev :
      H.levelMap (H.canonicalExtension F n).map (n + k) = ell := by
    rw [H.canonicalExtension_level_tail F n k]
    omega
  rw [← H.range_levelMap (H.canonicalExtension F n).map]
  exact ⟨n + k, hlev⟩

end SMTree
end SuccessorTree
