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
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hs)

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

/-- Number of missing target levels between consecutive source levels. -/
noncomputable def nextGap (H : SMTree S) (F : ShapeMap S) (m : Nat) : Nat :=
  H.levelMap F (m + 1) - (H.levelMap F m + 1)

/-- Repeatedly apply M2 until two consecutive source levels become consecutive
target levels, while preserving the already-fixed prefix. -/
theorem close_next_level
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (m : Nat) :
    ∃ G : ShapeMap S,
      G ∈ H.M ∧
      G.AgreesThrough F m ∧
      H.levelMap G (m + 1) = H.levelMap F m + 1 := by
  have aux :
      ∀ d : Nat, ∀ K : ShapeMap S, K ∈ H.M →
        nextGap H K m = d →
        ∃ G : ShapeMap S,
          G ∈ H.M ∧
          G.AgreesThrough K m ∧
          H.levelMap G (m + 1) = H.levelMap K m + 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro K hK hd
        have hmono :
            H.levelMap K m < H.levelMap K (m + 1) :=
          H.levelMap_strictMono K (Nat.lt_succ_self m)
        by_cases hclosed :
            H.levelMap K (m + 1) = H.levelMap K m + 1
        · exact ⟨K, hK, K.agreesThrough_refl m, hclosed⟩
        · have hgap :
              H.levelMap K m + 1 < H.levelMap K (m + 1) := by
            omega
          obtain ⟨K1, hK1, hK1agree, hK1next⟩ :=
            H.lower_next_level_once K hK m hgap
          have hK1base :
              H.levelMap K1 m = H.levelMap K m :=
            H.levelMap_eq_of_agreesThrough hK1agree le_rfl
          have hmeasure :
              nextGap H K1 m < d := by
            rw [← hd]
            unfold nextGap
            rw [hK1next, hK1base]
            omega
          obtain ⟨G, hG, hGagree, hGnext⟩ :=
            ih (nextGap H K1 m) hmeasure K1 hK1 rfl
          refine ⟨G, hG,
            ShapeMap.agreesThrough_trans hGagree hK1agree, ?_⟩
          rw [hGnext, hK1base]
  exact aux (nextGap H F m) F hF rfl

/-- A monoid member packaged with its membership proof. -/
structure MemberMap (H : SMTree S) where
  map : ShapeMap S
  mem : map ∈ H.M

namespace MemberMap

instance (H : SMTree S) : Coe (MemberMap H) (ShapeMap S) :=
  ⟨MemberMap.map⟩

end MemberMap

/-- Chosen gap-closed successor stage. -/
noncomputable def closeNextChoice
    (H : SMTree S) (X : MemberMap H) (m : Nat) : MemberMap H :=
  let h := H.close_next_level X.map X.mem m
  ⟨Classical.choose h, (Classical.choose_spec h).1⟩

theorem closeNextChoice_agrees
    (H : SMTree S) (X : MemberMap H) (m : Nat) :
    (H.closeNextChoice X m).map.AgreesThrough X.map m := by
  unfold closeNextChoice
  exact (Classical.choose_spec
    (H.close_next_level X.map X.mem m)).2.1

theorem closeNextChoice_level
    (H : SMTree S) (X : MemberMap H) (m : Nat) :
    H.levelMap (H.closeNextChoice X m).map (m + 1) =
      H.levelMap X.map m + 1 := by
  unfold closeNextChoice
  exact (Classical.choose_spec
    (H.close_next_level X.map X.mem m)).2.2

/-- Stages used to construct the canonical extension through source level n.
Before n the sequence is constant. Thereafter each stage closes the next
source-level gap. -/
noncomputable def canonicalStages
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    Nat → MemberMap H
  | 0 => ⟨F, hF⟩
  | i + 1 =>
      if i < n then
        canonicalStages H F hF n i
      else
        H.closeNextChoice (canonicalStages H F hF n i) i

/-- Underlying shape map at a canonical-extension stage. -/
noncomputable def canonicalSeq
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n i : Nat) :
    ShapeMap S :=
  (H.canonicalStages F hF n i).map

theorem canonicalSeq_mem
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n i : Nat) :
    H.canonicalSeq F hF n i ∈ H.M :=
  (H.canonicalStages F hF n i).mem

theorem canonicalSeq_succ_of_lt
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M)
    (n i : Nat) (hi : i < n) :
    H.canonicalSeq F hF n (i + 1) =
      H.canonicalSeq F hF n i := by
  simp [canonicalSeq, canonicalStages, hi]

theorem canonicalSeq_succ_agrees_of_le
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M)
    (n i : Nat) (hi : n ≤ i) :
    (H.canonicalSeq F hF n (i + 1)).AgreesThrough
      (H.canonicalSeq F hF n i) i := by
  have hnot : ¬ i < n := Nat.not_lt.mpr hi
  simp only [canonicalSeq, canonicalStages, hnot, ↓reduceIte]
  exact H.closeNextChoice_agrees
    (H.canonicalStages F hF n i) i

theorem canonicalSeq_next_level_of_le
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M)
    (n i : Nat) (hi : n ≤ i) :
    H.levelMap (H.canonicalSeq F hF n (i + 1)) (i + 1) =
      H.levelMap (H.canonicalSeq F hF n i) i + 1 := by
  have hnot : ¬ i < n := Nat.not_lt.mpr hi
  simp only [canonicalSeq, canonicalStages, hnot, ↓reduceIte]
  exact H.closeNextChoice_level
    (H.canonicalStages F hF n i) i

/-- All stages up through n are still the original map. -/
theorem canonicalSeq_apply_of_le
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M)
    (n i : Nat) (hi : i ≤ n) (a : T) :
    H.canonicalSeq F hF n i a = F a := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hin : i < n := by omega
      rw [H.canonicalSeq_succ_of_lt F hF n i hin]
      exact ih (by omega)

/-- The canonical stage sequence is a fusion-stable sequence. -/
theorem canonicalSeq_stable
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    ShapeMap.FusionStable (H.canonicalSeq F hF n) := by
  intro i a ha
  by_cases hi : i < n
  · rw [H.canonicalSeq_succ_of_lt F hF n i hi]
  · have hle : n ≤ i := Nat.le_of_not_gt hi
    exact (H.canonicalSeq_succ_agrees_of_le F hF n i hle a ha).symm

/-- The fusion limit which will be the canonical extension. -/
noncomputable def canonicalLimit
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    ShapeMap S :=
  ShapeMap.fusionLimit
    (H.canonicalSeq F hF n)
    (H.canonicalSeq_stable F hF n)

theorem canonicalLimit_mem
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    H.canonicalLimit F hF n ∈ H.M := by
  exact H.fusion_mem
    (H.canonicalSeq F hF n)
    (H.canonicalSeq_mem F hF n)
    (H.canonicalSeq_stable F hF n)

/-- The canonical fusion limit extends the original finite restriction. -/
theorem canonicalLimit_agrees
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    (H.canonicalLimit F hF n).AgreesThrough F n := by
  intro a ha
  calc
    H.canonicalLimit F hF n a =
        H.canonicalSeq F hF n n a := by
      exact ShapeMap.fusionLimit_eq_stage
        (H.canonicalSeq F hF n)
        (H.canonicalSeq_stable F hF n) ha
    _ = F a := H.canonicalSeq_apply_of_le F hF n n le_rfl a

/-- Diagonal target level at stage n+d. -/
theorem canonicalSeq_diagonal
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M)
    (n d : Nat) :
    H.levelMap (H.canonicalSeq F hF n (n + d)) (n + d) =
      H.levelMap F n + d := by
  induction d with
  | zero =>
      have hagree :
          (H.canonicalSeq F hF n n).AgreesThrough F n := by
        intro a ha
        exact H.canonicalSeq_apply_of_le F hF n n le_rfl a
      simpa using H.levelMap_eq_of_agreesThrough hagree le_rfl
  | succ d ih =>
      have hnle : n ≤ n + d := by omega
      have hstep :=
        H.canonicalSeq_next_level_of_le F hF n (n + d) hnle
      rw [ih] at hstep
      simpa [Nat.add_assoc] using hstep

/-- The fusion limit has the same diagonal level map as its stabilized stage. -/
theorem canonicalLimit_levelMap
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M)
    (n k : Nat) :
    H.levelMap (H.canonicalLimit F hF n) k =
      H.levelMap (H.canonicalSeq F hF n k) k := by
  obtain ⟨a, ha⟩ := H.level_nonempty k
  have hlim :
      H.canonicalLimit F hF n a =
        H.canonicalSeq F hF n k a := by
    exact ShapeMap.fusionLimit_eq_stage
      (H.canonicalSeq F hF n)
      (H.canonicalSeq_stable F hF n)
      (by simpa [ha])
  calc
    H.levelMap (H.canonicalLimit F hF n) k =
        LevelTree.lev (H.canonicalLimit F hF n a) := by
      simpa [ha] using
        H.levelMap_eq (H.canonicalLimit F hF n) (a := a)
    _ = LevelTree.lev (H.canonicalSeq F hF n k a) := by rw [hlim]
    _ = H.levelMap (H.canonicalSeq F hF n k) k := by
      simpa [ha] using
        (H.levelMap_eq (H.canonicalSeq F hF n k) (a := a)).symm

/-- Above the final target level of the approximation, the canonical limit
meets every target level. -/
theorem canonicalLimit_tailFull
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    ∀ ell : Nat, H.levelMap F n ≤ ell →
      ell ∈ (H.canonicalLimit F hF n).levelRange := by
  intro ell hell
  let d := ell - H.levelMap F n
  have hsum : H.levelMap F n + d = ell := by
    dsimp [d]
    exact Nat.add_sub_of_le hell
  have hdiag :
      H.levelMap (H.canonicalLimit F hF n) (n + d) = ell := by
    rw [H.canonicalLimit_levelMap F hF n (n + d)]
    rw [H.canonicalSeq_diagonal F hF n d]
    exact hsum
  have hrange :
      ell ∈ Set.range (H.levelMap (H.canonicalLimit F hF n)) :=
    ⟨n + d, hdiag⟩
  rw [H.range_levelMap (H.canonicalLimit F hF n)] at hrange
  exact hrange

/-- Existence part of Proposition 1.12, expressed for the restriction of a
chosen global monoid member. -/
theorem exists_canonicalExtension
    (H : SMTree S) (F : ShapeMap S) (hF : F ∈ H.M) (n : Nat) :
    ∃ G : ShapeMap S,
      G ∈ H.M ∧
      G.AgreesThrough F n ∧
      ∀ ell : Nat, H.levelMap F n ≤ ell → ell ∈ G.levelRange := by
  exact ⟨H.canonicalLimit F hF n,
    H.canonicalLimit_mem F hF n,
    H.canonicalLimit_agrees F hF n,
    H.canonicalLimit_tailFull F hF n⟩

end SMTree

end SuccessorTree
