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
  · constructor
    · intro x hx
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
    · have hcomp : F2 (F1 a) = F a :=
        hagree a (by omega)
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
      rw [hFa1, htarget, hFa]

end SMTree
end SuccessorTree
