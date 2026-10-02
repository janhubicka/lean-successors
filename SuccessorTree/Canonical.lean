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


/-- Tail-fullness forces a shape map to advance by exactly one target level
at every subsequent source level. -/
theorem levelMap_succ_of_tailFull
    (H : SMTree S) (G : ShapeMap S) (base k : Nat)
    (hfull : ∀ ell : Nat, base ≤ ell → ell ∈ G.levelRange)
    (hbase : base ≤ H.levelMap G k) :
    H.levelMap G (k + 1) = H.levelMap G k + 1 := by
  have hmem :
      H.levelMap G k + 1 ∈ Set.range (H.levelMap G) := by
    rw [H.range_levelMap G]
    exact hfull _ (by omega)
  rcases hmem with ⟨j, hj⟩
  have hstrict := H.levelMap_strictMono G
  have hlow := hstrict (Nat.lt_succ_self k)
  have hkj : k + 1 ≤ j := by
    by_contra h
    have hjk : j ≤ k := by omega
    have hle := hstrict.monotone hjk
    rw [hj] at hle
    omega
  have hup := hstrict.monotone hkj
  rw [hj] at hup
  exact le_antisymm hup (Nat.succ_le_of_lt hlow)

/-- When adjacent source levels map to adjacent target levels, weak successor
preservation is automatically exact on that edge. -/
theorem succ_eq_of_consecutive_levels
    (H : SMTree S) (G : ShapeMap S)
    {a b : T} {p : List T} {c : Label}
    (hsucc : S.succ a p c = some b)
    (hlevels :
      H.levelMap G (LevelTree.lev b) =
        H.levelMap G (LevelTree.lev a) + 1) :
    S.succ (G a) (p.map G) c = some (G b) := by
  obtain ⟨d, hd, hdb⟩ := G.weak_succ' hsucc
  have hcover : G a ⋖ d := S.covBy_of_succ_eq_some hd
  have hdlev :
      LevelTree.lev d = LevelTree.lev (G a) + 1 :=
    LevelTree.covBy_level_eq hcover
  have hsame :
      LevelTree.lev d = LevelTree.lev (G b) := by
    calc
      LevelTree.lev d = LevelTree.lev (G a) + 1 := hdlev
      _ = H.levelMap G (LevelTree.lev a) + 1 := by
        rw [← H.levelMap_eq G (a := a)]
      _ = H.levelMap G (LevelTree.lev b) := hlevels.symm
      _ = LevelTree.lev (G b) := H.levelMap_eq G (a := b)
  have hdeq : d = G b :=
    LevelTree.same_level_of_le hdb hsame
  simpa [hdeq] using hd

private theorem canonical_list_map_eq
    (p : List T) (F G : ShapeMap S)
    (h : ∀ x ∈ p, F x = G x) :
    p.map F = p.map G := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = G x := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = G y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

/-- Uniqueness principle behind Proposition 1.12.  Two shape maps which agree
on the prescribed source prefix and meet every target level above the common
top image are identical. -/
theorem shapeMap_unique_of_prefix_tailFull
    (H : SMTree S) (F G K : ShapeMap S) (n : Nat)
    (hGagree : ∀ a : T, LevelTree.lev a ≤ n → G a = F a)
    (hKagree : ∀ a : T, LevelTree.lev a ≤ n → K a = F a)
    (hGfull :
      ∀ ell : Nat, H.levelMap F n ≤ ell → ell ∈ G.levelRange)
    (hKfull :
      ∀ ell : Nat, H.levelMap F n ≤ ell → ell ∈ K.levelRange) :
    G.toFun = K.toFun := by
  have hGn :
      H.levelMap G n = H.levelMap F n := by
    obtain ⟨a, ha⟩ := H.level_nonempty n
    calc
      H.levelMap G n = LevelTree.lev (G a) := by
        simpa [ha] using H.levelMap_eq G (a := a)
      _ = LevelTree.lev (F a) := by
        rw [hGagree a (Nat.le_of_eq ha)]
      _ = H.levelMap F n := by
        simpa [ha] using (H.levelMap_eq F (a := a)).symm
  have hKn :
      H.levelMap K n = H.levelMap F n := by
    obtain ⟨a, ha⟩ := H.level_nonempty n
    calc
      H.levelMap K n = LevelTree.lev (K a) := by
        simpa [ha] using H.levelMap_eq K (a := a)
      _ = LevelTree.lev (F a) := by
        rw [hKagree a (Nat.le_of_eq ha)]
      _ = H.levelMap F n := by
        simpa [ha] using (H.levelMap_eq F (a := a)).symm

  have hpoint :
      ∀ k : Nat, ∀ a : T, LevelTree.lev a = k → G a = K a := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro a ha
        by_cases hkn : k ≤ n
        · have hale : LevelTree.lev a ≤ n := by
            simpa [ha] using hkn
          exact (hGagree a hale).trans (hKagree a hale).symm
        · have hnk : n < k := Nat.lt_of_not_ge hkn
          have hkpos : 0 < k := by omega
          let j := k - 1
          have hjlt : j < k := by
            dsimp [j]
            omega
          have hjle : j ≤ LevelTree.lev a := by
            rw [ha]
            dsimp [j]
            omega
          let x := LevelTree.ancestor a j hjle
          have hxa : x ≤ a :=
            LevelTree.ancestor_le a j hjle
          have hxlev : LevelTree.lev x = j :=
            LevelTree.level_ancestor a j hjle
          have hcover : x ⋖ a := by
            apply LevelTree.covBy_of_le_level_succ hxa
            rw [ha, hxlev]
            dsimp [j]
            omega
          obtain ⟨p, c, hsucc⟩ := S.s3 hcover
          have hxEq : G x = K x :=
            ih j hjlt x hxlev
          have hpEq : ∀ y ∈ p, G y = K y := by
            intro y hy
            have hyltx := S.parameter_level_lt hsucc hy
            have hyltk : LevelTree.lev y < k := by
              rw [hxlev] at hyltx
              exact hyltx.trans hjlt
            exact ih (LevelTree.lev y) hyltk y rfl
          have hpmap : p.map G = p.map K :=
            canonical_list_map_eq p G K hpEq
          have hnj : n ≤ j := by
            dsimp [j]
            omega
          have hGbase :
              H.levelMap F n ≤ H.levelMap G j := by
            calc
              H.levelMap F n = H.levelMap G n := hGn.symm
              _ ≤ H.levelMap G j :=
                (H.levelMap_strictMono G).monotone hnj
          have hKbase :
              H.levelMap F n ≤ H.levelMap K j := by
            calc
              H.levelMap F n = H.levelMap K n := hKn.symm
              _ ≤ H.levelMap K j :=
                (H.levelMap_strictMono K).monotone hnj
          have hGstep :=
            H.levelMap_succ_of_tailFull G
              (H.levelMap F n) j hGfull hGbase
          have hKstep :=
            H.levelMap_succ_of_tailFull K
              (H.levelMap F n) j hKfull hKbase
          have hka : k = j + 1 := by
            dsimp [j]
            omega
          have hGlevels :
              H.levelMap G (LevelTree.lev a) =
                H.levelMap G (LevelTree.lev x) + 1 := by
            rw [ha, hxlev, hka]
            exact hGstep
          have hKlevels :
              H.levelMap K (LevelTree.lev a) =
                H.levelMap K (LevelTree.lev x) + 1 := by
            rw [ha, hxlev, hka]
            exact hKstep
          have hGsucc :=
            H.succ_eq_of_consecutive_levels G hsucc hGlevels
          have hKsucc :=
            H.succ_eq_of_consecutive_levels K hsucc hKlevels
          have hsome : (some (G a) : Option T) = some (K a) := by
            calc
              some (G a) =
                  S.succ (G x) (p.map G) c := hGsucc.symm
              _ = S.succ (K x) (p.map K) c := by
                rw [hxEq, hpmap]
              _ = some (K a) := hKsucc
          exact Option.some.inj hsome
  funext a
  exact hpoint (LevelTree.lev a) a rfl

/-- Uniqueness clause of Proposition 1.12 for the current M-map
representation. -/
theorem canonicalExtension_unique
    (H : SMTree S) (F G : MMap H) (n : Nat)
    (hGagree : ∀ a : T, LevelTree.lev a ≤ n → G a = F a)
    (hGfull :
      ∀ ell : Nat, H.levelMap F.map n ≤ ell →
        ell ∈ G.map.levelRange) :
    G = H.canonicalExtension F n := by
  apply MMap.ext_map
  apply ShapeMap.ext_toFun
  exact H.shapeMap_unique_of_prefix_tailFull
    F.map G.map (H.canonicalExtension F n).map n
    hGagree
    (H.canonicalExtension_agrees F n)
    hGfull
    (H.canonicalExtension_tail_mem_levelRange F n)

end SMTree
end SuccessorTree
