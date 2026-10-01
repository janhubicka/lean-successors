import SuccessorTree.Monoid
import Mathlib.Tactic

/-!
# Finite one-level approximations for the successor-tree pigeonhole proof

For Lemma 3.1 of the paper we can represent a letter of the Hales--Jewett
alphabet by its canonical total extension.  Such a letter is an M-map which
skips only level n.  Words in the alphabet are then interpreted by composition.

This avoids quotienting partial maps while retaining exactly their restriction
to levels at most n.
-/

namespace SuccessorTree

namespace SMTree

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- A shape-preserving map together with the proof that it belongs to M. -/
structure MMap (H : SMTree S) where
  map : ShapeMap S
  mem : map ∈ H.M

namespace MMap

instance (H : SMTree S) : CoeFun (MMap H) (fun _ => T → T) :=
  ⟨fun F => F.map⟩

/-- Identity in the distinguished monoid. -/
def id (H : SMTree S) : MMap H where
  map := ShapeMap.id S
  mem := H.id_mem

/-- Composition in the distinguished monoid. -/
def comp (H : SMTree S) (F G : MMap H) : MMap H where
  map := F.map.comp G.map
  mem := H.comp_mem F.mem G.mem

@[simp] theorem id_apply (H : SMTree S) (a : T) :
    MMap.id H a = a := rfl

@[simp] theorem comp_apply (H : SMTree S) (F G : MMap H) (a : T) :
    MMap.comp H F G a = F (G a) := rfl

end MMap

/-- A letter of the Hales--Jewett alphabet at level n.

Via Proposition 1.12 in the paper, these are exactly the canonical total
extensions of members of AM^n_1 whose moving level lands on n+1.
-/
structure OneLevelLetter (H : SMTree S) (n : Nat) where
  toMMap : MMap H
  skips : toMMap.map.SkipsOnly n

namespace OneLevelLetter

instance (H : SMTree S) (n : Nat) :
    CoeFun (OneLevelLetter H n) (fun _ => T → T) :=
  ⟨fun e => e.toMMap⟩

@[simp] theorem level_apply (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) (a : T) :
    LevelTree.lev (e a) =
      if LevelTree.lev a < n then LevelTree.lev a else LevelTree.lev a + 1 := by
  calc
    LevelTree.lev (e a) =
        H.levelMap e.toMMap.map (LevelTree.lev a) :=
      (H.levelMap_eq e.toMMap.map (a := a)).symm
    _ = if LevelTree.lev a < n then LevelTree.lev a else LevelTree.lev a + 1 :=
      H.levelMap_of_skipsOnly e.toMMap.map n e.skips (LevelTree.lev a)

theorem eq_id_below (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) {a : T} (ha : LevelTree.lev a < n) :
    e a = a :=
  H.eq_id_below_skip e.toMMap.map n e.skips ha

theorem level_succ_at (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) {a : T} (ha : LevelTree.lev a = n) :
    LevelTree.lev (e a) = n + 1 := by
  rw [e.level_apply H, ha]
  simp

end OneLevelLetter

/-- Interpretation of a finite word as the canonical total extension g_w^+.

The order is the paper's order: if w=u^e, then g_w^+ = g_u^+ o e.
-/
def wordMap (H : SMTree S) (n : Nat) :
    List (OneLevelLetter H n) → MMap H
  | [] => MMap.id H
  | e :: w => MMap.comp H e.toMMap (wordMap H n w)

@[simp] theorem wordMap_nil_apply (H : SMTree S) (n : Nat) (a : T) :
    wordMap H n [] a = a := rfl

@[simp] theorem wordMap_cons_apply (H : SMTree S) (n : Nat)
    (e : OneLevelLetter H n) (w : List (OneLevelLetter H n)) (a : T) :
    wordMap H n (e :: w) a = e (wordMap H n w a) := by
  rfl

/-- Appending the last character agrees with the inductive definition in
Lemma 3.1. -/
theorem wordMap_append_singleton_apply (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) (e : OneLevelLetter H n) (a : T) :
    wordMap H n (w ++ [e]) a = wordMap H n w (e a) := by
  induction w generalizing a with
  | nil =>
      simp
  | cons d w ih =>
      simp only [List.cons_append, wordMap_cons_apply]
      rw [ih]

/-- Every word map is literally the identity below the fixed level n. -/
theorem wordMap_eq_id_below (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) {a : T}
    (ha : LevelTree.lev a < n) :
    wordMap H n w a = a := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      rw [wordMap_cons_apply, ih]
      exact e.eq_id_below H ha

/-- On level n, each additional letter raises the image level by exactly one. -/
theorem level_wordMap_at (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) {a : T}
    (ha : LevelTree.lev a = n) :
    LevelTree.lev (wordMap H n w a) = n + w.length := by
  induction w with
  | nil =>
      simpa [ha]
  | cons e w ih =>
      rw [wordMap_cons_apply]
      have htail : LevelTree.lev (wordMap H n w a) = n + w.length := ih
      rw [e.level_apply H, htail]
      have hnot : ¬ n + w.length < n := by omega
      simp [hnot]
      omega

/-- Restriction to the finite initial segment T(<=n). -/
abbrev RestrictedMap (T : Type u) [PartialOrder T] [LevelTree T] (n : Nat) :=
  {a : T // LevelTree.lev a ≤ n} → T

/-- The finite approximation represented by a monoid map. -/
def MMap.restrictLe (H : SMTree S) (n : Nat) (F : MMap H) :
    RestrictedMap T n :=
  fun a => F a.1

/-- The paper's g_w, represented as a restriction of the total word map. -/
def wordApprox (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) : RestrictedMap T n :=
  (wordMap H n w).restrictLe H n

@[simp] theorem wordApprox_apply (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) (a : {a : T // LevelTree.lev a ≤ n}) :
    wordApprox H n w a = wordMap H n w a.1 := rfl

/-- On levels below n, every word approximation is the identity. -/
theorem wordApprox_eq_id_below (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n))
    (a : {a : T // LevelTree.lev a ≤ n})
    (ha : LevelTree.lev a.1 < n) :
    wordApprox H n w a = a.1 :=
  wordMap_eq_id_below H n w ha

end SMTree

end SuccessorTree
