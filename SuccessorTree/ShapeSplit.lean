import SuccessorTree.Canonical
import Mathlib.Tactic

/-!
# Finite target-level shape splitting

This is the M1--M2 finite factorisation behind Proposition shape-split
in the manuscript.  The useful formal statement is existential: lower the
image of the last source level to an admissible target cut, preserving every
lower source level, and retain the outer M-factor.

The concrete ancestor formula for the truncated top level follows afterwards
from comparability and equality of levels.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- At the root source level, every level strictly below the root image is
skipped by the map. -/
theorem skips_below_levelMap_zero
    (H : SMTree S) (F : MMap H) {q : Nat}
    (hq : q < H.levelMap F.map 0) :
    F.map.Skips q := by
  intro hqmem
  rw [← H.range_levelMap F.map] at hqmem
  rcases hqmem with ⟨j, hj⟩
  have hmono := (H.levelMap_strictMono F.map).monotone (Nat.zero_le j)
  rw [hj] at hmono
  omega

/-- One M2 step lowers the image of source level 0 by one, with an explicit
outer one-level factor. -/
theorem exists_lower_root_once_factor
    (H : SMTree S) (F : MMap H)
    (hpos : 0 < H.levelMap F.map 0) :
    ∃ G D : MMap H,
      D.map.SkipsOnly (H.levelMap F.map 0 - 1) ∧
      (∀ x : T, LevelTree.lev x = 0 → D (G x) = F x) ∧
      H.levelMap G.map 0 = H.levelMap F.map 0 - 1 := by
  obtain ⟨a, ha⟩ := H.level_nonempty 0
  have hFa :
      LevelTree.lev (F a) = H.levelMap F.map 0 := by
    simpa [ha] using (H.levelMap_eq F.map (a := a)).symm
  have hskip :
      F.map.Skips (LevelTree.lev (F a) - 1) := by
    rw [hFa]
    apply H.skips_below_levelMap_zero F
    omega
  obtain ⟨F1, F2, hF1, hF2, hF2skip, hagree⟩ :=
    H.m2 0 F.map F.mem a ha (by simpa [hFa] using hpos) hskip
  let G : MMap H := ⟨F1, hF1⟩
  let D : MMap H := ⟨F2, hF2⟩
  have hcomp : F2 (F1 a) = F a := hagree a (by simpa [ha])
  have hG0 :
      H.levelMap G.map 0 = H.levelMap F.map 0 - 1 := by
    have hF1a :
        LevelTree.lev (F1 a) = H.levelMap G.map 0 := by
      simpa [G, ha] using (H.levelMap_eq F1 (a := a)).symm
    have htarget :
        LevelTree.lev (F1 a) = LevelTree.lev (F a) - 1 := by
      have hlev :
          LevelTree.lev (F2 (F1 a)) =
            if LevelTree.lev (F1 a) < LevelTree.lev (F a) - 1
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
      H.levelMap G.map 0 = LevelTree.lev (F1 a) := hF1a.symm
      _ = LevelTree.lev (F a) - 1 := htarget
      _ = H.levelMap F.map 0 - 1 := by rw [hFa]
  refine ⟨G, D, ?_, ?_, hG0⟩
  · simpa [D, hFa] using hF2skip
  · intro x hx
    exact hagree x (by simpa [hx])

/-- Admissibility of a target cut for truncating source level n.

At n=0 there is no lower source level.  At n+1 the cut must lie strictly
above the image of level n, exactly as in Proposition shape-split. -/
def SplitCut
    (H : SMTree S) (F : MMap H) (n m : Nat) : Prop :=
  m ≤ H.levelMap F.map n ∧
    match n with
    | 0 => True
    | j + 1 => H.levelMap F.map j < m

/-- M1--M2 shape splitting in factorised form.

The map P is the target truncation of F at its last source level; Q is the
outer factor.  Q fixes every target level strictly below m. -/
theorem exists_shapeSplit_factor
    (H : SMTree S) (F : MMap H) (n m : Nat)
    (hcut : SplitCut H F n m) :
    ∃ P Q : MMap H,
      (∀ x : T, LevelTree.lev x < n → P x = F x) ∧
      H.levelMap P.map n = m ∧
      Q.FixesBelow H m ∧
      (∀ x : T, LevelTree.lev x ≤ n → Q (P x) = F x) := by
  generalize htop : H.levelMap F.map n = q
  induction q using Nat.strong_induction_on generalizing F with
  | h q ih =>
      have hmq : m ≤ q := by
        simpa [htop] using hcut.1
      by_cases heq : q = m
      · refine ⟨F, MMap.id H, ?_, ?_, ?_, ?_⟩
        · intro x hx
          rfl
        · exact htop.trans heq
        · exact MMap.id_fixesBelow H m
        · intro x hx
          rfl
      · have hmq' : m < q := lt_of_le_of_ne hmq (Ne.symm heq)
        cases n with
        | zero =>
            obtain ⟨G, D, hDskip, hDG, hG0⟩ :=
              H.exists_lower_root_once_factor F (by omega)
            have hGlt : H.levelMap G.map 0 < q := by
              rw [hG0, htop]
              omega
            have hcutG : SplitCut H G 0 m := by
              refine ⟨?_, trivial⟩
              rw [hG0, htop]
              omega
            obtain ⟨P, Q, hPagree, hPtop, hQfix, hQP⟩ :=
              ih (H.levelMap G.map 0) hGlt G hcutG rfl
            let R : MMap H := MMap.comp H D Q
            refine ⟨P, R, ?_, hPtop, ?_, ?_⟩
            · intro x hx
              omega
            · intro x hx
              have hQx : Q x = x := hQfix x hx
              have hDcut : m ≤ H.levelMap F.map 0 - 1 := by
                rw [htop]
                omega
              have hDx : D x = x := by
                apply H.eq_id_below_skip D.map
                  (H.levelMap F.map 0 - 1) hDskip
                exact lt_of_lt_of_le hx hDcut
              change D (Q x) = x
              rw [hQx, hDx]
            · intro x hx
              change D (Q (P x)) = F x
              rw [hQP x hx]
              exact hDG x (by omega)
        | succ j =>
            have hlowF : H.levelMap F.map j < m := hcut.2
            have hgap :
                H.levelMap F.map j + 1 <
                  H.levelMap F.map (j + 1) := by
              rw [htop]
              omega
            obtain ⟨G, D, hGagree, hDskip, hDG, hGnext⟩ :=
              H.exists_lower_gap_once_factor F j hgap
            have hGj :
                H.levelMap G.map j = H.levelMap F.map j := by
              obtain ⟨x, hx⟩ := H.level_nonempty j
              calc
                H.levelMap G.map j = LevelTree.lev (G x) := by
                  simpa [hx] using H.levelMap_eq G.map (a := x)
                _ = LevelTree.lev (F x) := by
                  rw [hGagree x (by simpa [hx])]
                _ = H.levelMap F.map j := by
                  simpa [hx] using (H.levelMap_eq F.map (a := x)).symm
            have hGlt : H.levelMap G.map (j + 1) < q := by
              rw [hGnext, htop]
              omega
            have hcutG : SplitCut H G (j + 1) m := by
              refine ⟨?_, ?_⟩
              · rw [hGnext, htop]
                omega
              · simpa [hGj] using hlowF
            obtain ⟨P, Q, hPagree, hPtop, hQfix, hQP⟩ :=
              ih (H.levelMap G.map (j + 1)) hGlt G hcutG rfl
            let R : MMap H := MMap.comp H D Q
            refine ⟨P, R, ?_, hPtop, ?_, ?_⟩
            · intro x hx
              exact (hPagree x hx).trans (hGagree x (by omega))
            · intro x hx
              have hQx : Q x = x := hQfix x hx
              have hDcut :
                  m ≤ H.levelMap F.map (j + 1) - 1 := by
                rw [htop]
                omega
              have hDx : D x = x := by
                apply H.eq_id_below_skip D.map
                  (H.levelMap F.map (j + 1) - 1) hDskip
                exact lt_of_lt_of_le hx hDcut
              change D (Q x) = x
              rw [hQx, hDx]
            · intro x hx
              change D (Q (P x)) = F x
              rw [hQP x hx]
              exact hDG x hx

end SMTree
end SuccessorTree
