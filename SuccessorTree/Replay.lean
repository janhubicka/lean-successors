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

/-- A chosen occurrence of a supported letter inside the star prefix. -/
structure SupportOccurrence (s : List α) (e : α) where
  before : List α
  after : List α
  eq_word : s = before ++ e :: after

noncomputable def supportOccurrence
    (s : List α) (hs : Supports s) (e : α) :
    SupportOccurrence s e := by
  classical
  obtain ⟨u, v, huv⟩ := exists_split_of_mem (hs e)
  exact ⟨u, v, huv⟩

theorem supportOccurrence_before_lt
    (s : List α) (hs : Supports s) (e : α) :
    (supportOccurrence s hs e).before.length < s.length := by
  have hspec := (supportOccurrence s hs e).eq_word
  rw [hspec]
  simp
  omega

/-- Source base level of the edge represented by a raw line symbol.

A parameter reuses the first parameter edge, whose base comes after the whole
star prefix. A constant reuses its chosen earlier support occurrence.
-/
noncomputable def replaySource
    (n : Nat) (s : List (OneLevelLetter H n))
    (hs : Supports s) :
    LineSymbol (OneLevelLetter H n) → Nat
  | .parameter => n + s.length
  | .const e => n + (supportOccurrence s hs e).before.length

theorem replaySource_lt
    (H : SMTree S) {n : Nat}
    (s : List (OneLevelLetter H n))
    (hs : Supports s)
    (k : Nat) (x : LineSymbol (OneLevelLetter H n)) :
    replaySource n s hs x < n + s.length + 1 + k := by
  cases x with
  | parameter =>
      simp [replaySource]
      omega
  | const e =>
      have hlt := supportOccurrence_before_lt s hs e
      simp [replaySource]
      omega

/-- M3 duplication used for the k-th symbol after the first parameter. -/
noncomputable def replayDup
    (H : SMTree S) {n : Nat}
    (s : List (OneLevelLetter H n))
    (hs : Supports s)
    (k : Nat) (x : LineSymbol (OneLevelLetter H n)) :
    MMap H :=
  H.duplicate
    (replaySource n s hs x)
    (n + s.length + 1 + k)
    (H.replaySource_lt s hs k x)

/-- Fold the M3 replay duplications through the raw tail after the first
parameter. -/
noncomputable def replayTail
    (H : SMTree S) {n : Nat}
    (s : List (OneLevelLetter H n))
    (hs : Supports s) :
    Nat → List (LineSymbol (OneLevelLetter H n)) → MMap H → MMap H
  | _, [], B => B
  | k, x :: xs, B =>
      replayTail H s hs (k + 1) xs
        (MMap.comp H (H.replayDup s hs k x) B)

/-- Final total replay block attached to a supported starred line. -/
noncomputable def replayMap
    (H : SMTree S) {n : Nat}
    (L : StarLine (OneLevelLetter H n))
    (hs : Supports L.star) : MMap H :=
  replayTail H L.star hs 0 (afterFirstParameter L.word)
    (wordMap H n L.star)

/-- Every remaining duplication is invisible below its current target level. -/
theorem replayTail_apply_of_level_lt
    (H : SMTree S) {n : Nat}
    (s : List (OneLevelLetter H n))
    (hs : Supports s)
    (k : Nat) (xs : List (LineSymbol (OneLevelLetter H n)))
    (B : MMap H) (a : T)
    (ha : LevelTree.lev (B a) < n + s.length + 1 + k) :
    replayTail H s hs k xs B a = B a := by
  induction xs generalizing k B with
  | nil =>
      rfl
  | cons x xs ih =>
      let D := H.replayDup s hs k x
      have hD : D (B a) = B a := by
        apply H.duplicate_eq_id_below
        exact ha
      change
        replayTail H s hs (k + 1) xs
            (MMap.comp H D B) a =
          B a
      have hcomp : MMap.comp H D B a = B a := by
        simpa [D] using hD
      rw [ih]
      · exact hcomp
      · rw [hcomp]
        omega

/-- The replay map agrees with g_{L(*)} on the whole base restriction
T(<=n). -/
theorem replayMap_base
    (H : SMTree S) {n : Nat}
    (L : StarLine (OneLevelLetter H n))
    (hs : Supports L.star)
    (a : {a : T // LevelTree.lev a ≤ n}) :
    H.replayMap L hs a.1 = wordMap H n L.star a.1 := by
  unfold replayMap
  apply H.replayTail_apply_of_level_lt
  by_cases hlt : LevelTree.lev a.1 < n
  · rw [wordMap_eq_id_below H n L.star hlt]
    omega
  · have heq : LevelTree.lev a.1 = n := by omega
    rw [H.level_wordMap_at n L.star heq]
    omega

/-- Replay one earlier occurrence of a letter by M3.

If the source occurrence follows a prefix u, then its source base is on level
n + |u|.  Thus replaying the same successor transition at a node b of level m
uses the duplication map F_m^(n+|u|).  This is the indexing needed in the
proof of Lemma 3.1.
-/
theorem duplicate_word_occurrence
    (H : SMTree S) {n : Nat}
    (u v : List (OneLevelLetter H n))
    (e : OneLevelLetter H n)
    (a b : T)
    (ha : LevelTree.lev a = n)
    (hb : LevelTree.lev b = m)
    (hsourceTarget : n + u.length < m)
    (hbelow :
      wordMap H n (u ++ [e]) a ≤ b) :
    S.succ b
        (H.letterCode e a ha).params
        (H.letterCode e a ha).char =
      some (H.duplicate (n + u.length) m hsourceTarget b) := by
  have hbase :
      LevelTree.lev (wordMap H n u a) = n + u.length :=
    H.level_wordMap_at n u ha
  have hedge :=
    H.wordMap_append_letter_succ u e a ha
  exact H.duplicate_rule
    (n + u.length) m hsourceTarget
    (wordMap H n u a) b
    (H.letterCode e a ha).params
    (H.letterCode e a ha).char
    (wordMap H n (u ++ [e]) a)
    hbase hb hedge hbelow

/-- Specialization when b is the endpoint of a longer word containing that
occurrence. -/
theorem duplicate_occurrence_at_word_endpoint
    (H : SMTree S) {n : Nat}
    (u v : List (OneLevelLetter H n))
    (e : OneLevelLetter H n)
    (a : T) (ha : LevelTree.lev a = n)
    (hlt : n + u.length <
      n + (u ++ e :: v).length) :
    S.succ (wordMap H n (u ++ e :: v) a)
        (H.letterCode e a ha).params
        (H.letterCode e a ha).char =
      some
        (H.duplicate
          (n + u.length)
          (n + (u ++ e :: v).length)
          hlt
          (wordMap H n (u ++ e :: v) a)) := by
  apply H.duplicate_word_occurrence u v e a
  · exact H.level_wordMap_at n (u ++ e :: v) ha
  · exact hlt
  · exact H.wordMap_append_letter_le u v e a ha

end SMTree

end SuccessorTree
