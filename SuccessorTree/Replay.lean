import SuccessorTree.Approximation
import Mathlib.Tactic

/-!
# Duplication and successor codes for replay

This file packages the two ingredients used repeatedly in the proof of
Lemma 3.1:

* the M3 duplication map F_m^n;
* the decomposition data Dp/Dc of a one-step successor.

The actual replay recursion is built in the next layer.
-/

namespace SuccessorTree

namespace SMTree

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Successor decomposition data for a fixed edge a <. b. -/
structure SuccCode (S : STree T Label) (a b : T) where
  params : List T
  char : Label
  succ_eq : S.succ a params char = some b

/-- S3 supplies successor code for every cover. -/
noncomputable def succCodeOfCovBy (S : STree T Label)
    {a b : T} (h : a ⋖ b) : SuccCode S a b := by
  classical
  obtain ⟨p, c, hc⟩ := S.s3 h
  exact ⟨p, c, hc⟩

@[simp] theorem succCodeOfCovBy_eq (S : STree T Label)
    {a b : T} (h : a ⋖ b) :
    S.succ a (succCodeOfCovBy S h).params
      (succCodeOfCovBy S h).char = some b :=
  (succCodeOfCovBy S h).succ_eq

/-- The skipped-level image of a letter is an immediate successor of the
original node. -/
theorem letter_covBy (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) {a : T}
    (ha : LevelTree.lev a = n) :
    a ⋖ e a := by
  have hle : a ≤ e a :=
    H.le_apply_at_skip e.toMMap.map n e.skips ha
  have hlev : LevelTree.lev (e a) = LevelTree.lev a + 1 := by
    rw [e.level_succ_at H ha, ha]
  exact LevelTree.covBy_of_le_level_succ hle hlev

/-- Dp/Dc for the node e(a), where e is a one-level Hales--Jewett letter. -/
noncomputable def letterCode (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) (a : T)
    (ha : LevelTree.lev a = n) : SuccCode S a (e a) :=
  succCodeOfCovBy S (H.letter_covBy e ha)

/-- A node on level n+1, decomposed over its level-n predecessor. -/
noncomputable def topCode (H : SMTree S) (n : Nat)
    (b : T) (hb : LevelTree.lev b = n + 1) :
    SuccCode S (LevelTree.ancestor b n (by omega)) b := by
  let a := LevelTree.ancestor b n (by omega : n ≤ LevelTree.lev b)
  have hab : a ≤ b := LevelTree.ancestor_le b n (by omega)
  have halev : LevelTree.lev a = n := LevelTree.level_ancestor b n (by omega)
  have hcov : a ⋖ b := by
    apply LevelTree.covBy_of_le_level_succ hab
    omega
  exact succCodeOfCovBy S hcov

/-- A chosen M3 duplication map F_m^n. -/
noncomputable def duplicate (H : SMTree S)
    (n m : Nat) (hnm : n < m) : MMap H where
  map := Classical.choose (H.m3 n m hnm)
  mem := (Classical.choose_spec (H.m3 n m hnm)).1

theorem duplicate_skips (H : SMTree S)
    (n m : Nat) (hnm : n < m) :
    (H.duplicate n m hnm).map.SkipsOnly m :=
  (Classical.choose_spec (H.m3 n m hnm)).2.1

/-- Exact M3 duplication rule for the chosen map. -/
theorem duplicate_rule (H : SMTree S)
    (n m : Nat) (hnm : n < m)
    (a b : T) (p : List T) (c : Label) (s : T)
    (ha : LevelTree.lev a = n)
    (hb : LevelTree.lev b = m)
    (hs : S.succ a p c = some s)
    (hsb : s ≤ b) :
    S.succ b p c = some (H.duplicate n m hnm b) :=
  (Classical.choose_spec (H.m3 n m hnm)).2.2 a b p c s ha hb hs hsb

/-- Duplication is identity below its target level. -/
theorem duplicate_eq_id_below (H : SMTree S)
    (n m : Nat) (hnm : n < m)
    {a : T} (ha : LevelTree.lev a < m) :
    H.duplicate n m hnm a = a :=
  H.eq_id_below_skip (H.duplicate n m hnm).map m
    (H.duplicate_skips n m hnm) ha

/-- Duplication raises the target level by one. -/
theorem duplicate_level_at (H : SMTree S)
    (n m : Nat) (hnm : n < m)
    {a : T} (ha : LevelTree.lev a = m) :
    LevelTree.lev (H.duplicate n m hnm a) = m + 1 := by
  calc
    LevelTree.lev (H.duplicate n m hnm a) =
        H.levelMap (H.duplicate n m hnm).map (LevelTree.lev a) :=
      (H.levelMap_eq (H.duplicate n m hnm).map (a := a)).symm
    _ = LevelTree.lev a + 1 := by
      rw [H.levelMap_of_skipsOnly (H.duplicate n m hnm).map m
        (H.duplicate_skips n m hnm)]
      simp [ha]
    _ = m + 1 := by rw [ha]

end SMTree

end SuccessorTree
