import SuccessorTree.Monoid
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Local canonical extension

For the one-dimensional pigeonhole proof we only need the one-step part of
Proposition 1.12: after fixing a map through source level n, we may choose an
M-extension whose next target level is exactly one higher.

The proof uses minimality of the next target level and one application of M2.
-/

namespace SuccessorTree

namespace ShapeMap

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Two maps agree on every source node through level n. -/
def AgreesThrough (F G : ShapeMap S) (n : Nat) : Prop :=
  ∀ a : T, LevelTree.lev a ≤ n → F a = G a

theorem agreesThrough_refl (F : ShapeMap S) (n : Nat) :
    F.AgreesThrough F n := by
  intro a ha
  rfl

theorem AgreesThrough.symm {F G : ShapeMap S} {n : Nat}
    (h : F.AgreesThrough G n) :
    G.AgreesThrough F n := by
  intro a ha
  exact (h a ha).symm

theorem AgreesThrough.trans {F G K : ShapeMap S} {n : Nat}
    (hFG : F.AgreesThrough G n)
    (hGK : G.AgreesThrough K n) :
    F.AgreesThrough K n := by
  intro a ha
  exact (hFG a ha).trans (hGK a ha)

end ShapeMap

namespace SMTree

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Agreement through a source level implies equality of the induced target
level at that source level. -/
theorem levelMap_eq_of_agreesThrough
    (H : SMTree S) {F G : ShapeMap S} {n : Nat}
    (h : F.AgreesThrough G n) :
    H.levelMap F n = H.levelMap G n := by
  obtain ⟨a, ha⟩ := H.level_nonempty n
  have hFG : F a = G a := h a (by simpa [ha])
  calc
    H.levelMap F n = LevelTree.lev (F a) := by
      simpa [ha] using H.levelMap_eq F (a := a)
    _ = LevelTree.lev (G a) := congrArg LevelTree.lev hFG
    _ = H.levelMap G n := by
      simpa [ha] using (H.levelMap_eq G (a := a)).symm

/-- If there is a gap after source level n, M2 lowers the next target level by
one while preserving the map through n. -/
theorem exists_reduce_next
    (H : SMTree S) (F : ShapeMap S) (hFmem : F ∈ H.M) (n : Nat)
    (hgap : H.levelMap F n + 1 < H.levelMap F (n + 1)) :
    ∃ F1 : ShapeMap S,
      F1 ∈ H.M ∧
      F1.AgreesThrough F n ∧
      H.levelMap F1 (n + 1) = H.levelMap F (n + 1) - 1 := by
  let r := H.levelMap F n
  let t := H.levelMap F (n + 1)

  have hrt : r < t - 1 := by
    dsimp [r, t]
    omega

  have hskip : F.Skips (t - 1) := by
    intro hmem
    have hmem' : t - 1 ∈ Set.range (H.levelMap F) := by
      rw [H.range_levelMap F]
      exact hmem
    rcases hmem' with ⟨j, hj⟩
    have hmono := H.levelMap_strictMono F
    by_cases hjlt : j < n + 1
    · have hjle : j ≤ n := by omega
      have hle := hmono.monotone hjle
      rw [hj] at hle
      dsimp [r, t] at hrt
      omega
    · by_cases hjeq : j = n + 1
      · subst j
        dsimp [t] at hj
        omega
      · have hjgt : n + 1 < j := by omega
        have hlt := hmono hjgt
        rw [hj] at hlt
        dsimp [t] at hlt
        omega

  obtain ⟨a, ha⟩ := H.level_nonempty (n + 1)
  have hFaLevel : LevelTree.lev (F a) = t := by
    have h := H.levelMap_eq F (a := a)
    rw [ha] at h
    exact h.symm
  have htpos : 0 < LevelTree.lev (F a) := by
    rw [hFaLevel]
    have hmono := H.levelMap_strictMono F (Nat.zero_lt_succ n)
    dsimp [t]
    exact lt_of_le_of_lt (Nat.zero_le _) hmono

  obtain ⟨F1, F2, hF1mem, hF2mem, hF2skip, hcomp⟩ :=
    H.m2 (n + 1) F hFmem a ha htpos (by
      simpa [hFaLevel] using hskip)
  have hF2skipT : F2.SkipsOnly (t - 1) := by
    simpa [hFaLevel] using hF2skip

  have hF1Next :
      H.levelMap F1 (n + 1) = t - 1 := by
    let q := H.levelMap F1 (n + 1)
    have hF1a : H.levelMap F1 (n + 1) = LevelTree.lev (F1 a) := by
      simpa [ha] using H.levelMap_eq F1 (a := a)
    have hcompa : F2 (F1 a) = F a := hcomp a (by simpa [ha])
    have hlevelComp :
        H.levelMap F2 q = t := by
      calc
        H.levelMap F2 q =
            H.levelMap F2 (LevelTree.lev (F1 a)) := by
              rw [← hF1a]
        _ = LevelTree.lev (F2 (F1 a)) :=
              H.levelMap_eq F2 (a := F1 a)
        _ = LevelTree.lev (F a) := congrArg LevelTree.lev hcompa
        _ = t := hFaLevel
    rw [H.levelMap_of_skipsOnly F2 (t - 1) hF2skipT] at hlevelComp
    by_cases hq : q < t - 1
    · simp [hq] at hlevelComp
      omega
    · simp [hq] at hlevelComp
      dsimp [q]
      omega

  have hAgree : F1.AgreesThrough F n := by
    intro x hx
    have hcompx : F2 (F1 x) = F x :=
      hcomp x (by omega)
    have hFxLe : LevelTree.lev (F x) ≤ r := by
      calc
        LevelTree.lev (F x) =
            H.levelMap F (LevelTree.lev x) :=
              (H.levelMap_eq F (a := x)).symm
        _ ≤ H.levelMap F n :=
              (H.levelMap_strictMono F).monotone hx
        _ = r := rfl
    let qx := LevelTree.lev (F1 x)
    have hlevelComp :
        H.levelMap F2 qx = LevelTree.lev (F x) := by
      calc
        H.levelMap F2 qx =
            LevelTree.lev (F2 (F1 x)) :=
              H.levelMap_eq F2 (a := F1 x)
        _ = LevelTree.lev (F x) := congrArg LevelTree.lev hcompx
    have hqx : qx < t - 1 := by
      by_contra hnot
      have hge : t - 1 ≤ qx := Nat.le_of_not_gt hnot
      rw [H.levelMap_of_skipsOnly F2 (t - 1) hF2skipT] at hlevelComp
      simp [Nat.not_lt.mpr hge] at hlevelComp
      dsimp [qx] at hlevelComp
      omega
    have hfix : F2 (F1 x) = F1 x :=
      H.eq_id_below_skip F2 (t - 1) hF2skipT hqx
    exact hfix.symm.trans hcompx

  refine ⟨F1, hF1mem, hAgree, ?_⟩
  simpa [t] using hF1Next

/-- One-step canonical extension: preserve F through level n and close the
next target-level gap. -/
theorem exists_tight_next
    (H : SMTree S) (F : ShapeMap S) (hFmem : F ∈ H.M) (n : Nat) :
    ∃ G : ShapeMap S,
      G ∈ H.M ∧
      G.AgreesThrough F n ∧
      H.levelMap G (n + 1) = H.levelMap G n + 1 := by
  classical
  let P : Nat → Prop := fun t =>
    ∃ G : ShapeMap S,
      G ∈ H.M ∧
      G.AgreesThrough F n ∧
      H.levelMap G (n + 1) = t
  have hP : ∃ t : Nat, P t := by
    refine ⟨H.levelMap F (n + 1), F, hFmem,
      ShapeMap.agreesThrough_refl F n, rfl⟩
  let t := Nat.find hP
  obtain ⟨G, hGmem, hGF, hGt⟩ := Nat.find_spec hP

  have htight :
      H.levelMap G (n + 1) = H.levelMap G n + 1 := by
    by_contra hne
    have hmono := H.levelMap_strictMono G (Nat.lt_succ_self n)
    have hgap : H.levelMap G n + 1 < H.levelMap G (n + 1) := by
      omega
    obtain ⟨G1, hG1mem, hG1G, hred⟩ :=
      H.exists_reduce_next G hGmem n hgap
    have hG1F : G1.AgreesThrough F n :=
      hG1G.trans hGF
    have hPrev : P (t - 1) := by
      refine ⟨G1, hG1mem, hG1F, ?_⟩
      rw [hred, hGt]
    have hmin := Nat.find_min' hP hPrev
    dsimp [t] at hmin
    have htpos : 0 < Nat.find hP := by
      rw [← hGt]
      exact lt_of_le_of_lt (Nat.zero_le _) hmono
    omega

  exact ⟨G, hGmem, hGF, htight⟩

end SMTree

end SuccessorTree
