import SuccessorTree.Approximation
import SuccessorTree.Pigeonhole
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

/-- One M3 replay step reproduces the next evaluated line symbol.

The current ordinary word w is assumed to extend the first-parameter prefix
s ++ [e] and to have the length corresponding to replay stage k.
-/
theorem replayDup_step
    (H : SMTree S) {n : Nat}
    (s : List (OneLevelLetter H n))
    (hs : Supports s)
    (e : OneLevelLetter H n)
    (a : T) (ha : LevelTree.lev a = n)
    (k : Nat)
    (w : List (OneLevelLetter H n))
    (hlen : w.length = s.length + 1 + k)
    (hprefix : s ++ [e] <+: w)
    (x : LineSymbol (OneLevelLetter H n)) :
    S.succ (wordMap H n w a)
        (H.letterCode (LineSymbol.eval e x) a ha).params
        (H.letterCode (LineSymbol.eval e x) a ha).char =
      some
        ((H.replayDup s hs k x)
          (wordMap H n w a)) := by
  have hb :
      LevelTree.lev (wordMap H n w a) =
        n + s.length + 1 + k := by
    rw [H.level_wordMap_at n w ha, hlen]
    omega
  have hstarPrefix : s <+: w := by
    exact (s.prefix_append [e]).trans hprefix
  cases x with
  | parameter =>
      have hbelow :
          wordMap H n (s ++ [e]) a ≤ wordMap H n w a :=
        H.wordMap_le_of_prefix hprefix a ha
      have hlt :
          n + s.length < n + s.length + 1 + k := by omega
      have hdup :=
        H.duplicate_word_occurrence
          s ([] : List (OneLevelLetter H n)) e a
          (wordMap H n w a) ha hb hlt hbelow
      simpa [replayDup, replaySource] using hdup
  | const d =>
      let occ := supportOccurrence s hs d
      have hspec : s = occ.before ++ d :: occ.after :=
        occ.eq_word
      have hocc :
          wordMap H n (occ.before ++ [d]) a ≤ wordMap H n s a := by
        have h :=
          H.wordMap_append_letter_le
            occ.before occ.after d a ha
        simpa [hspec] using h
      have hstar :
          wordMap H n s a ≤ wordMap H n w a :=
        H.wordMap_le_of_prefix hstarPrefix a ha
      have hbelow :
          wordMap H n (occ.before ++ [d]) a ≤ wordMap H n w a :=
        hocc.trans hstar
      have hlt :
          n + occ.before.length < n + s.length + 1 + k := by
        have ho := supportOccurrence_before_lt s hs d
        omega
      have hdup :=
        H.duplicate_word_occurrence
          occ.before occ.after d a
          (wordMap H n w a) ha hb hlt hbelow
      simpa [replayDup, replaySource, occ] using hdup

/-- Inductive correctness of the tail replay on a genuine letter input. -/
theorem replayTail_letter
    (H : SMTree S) {n : Nat}
    (s : List (OneLevelLetter H n))
    (hs : Supports s)
    (e : OneLevelLetter H n)
    (a : T) (ha : LevelTree.lev a = n)
    (k : Nat)
    (xs : List (LineSymbol (OneLevelLetter H n)))
    (B : MMap H)
    (w : List (OneLevelLetter H n))
    (hlen : w.length = s.length + 1 + k)
    (hprefix : s ++ [e] <+: w)
    (hB : B (e a) = wordMap H n w a) :
    replayTail H s hs k xs B (e a) =
      wordMap H n (w ++ evalWord e xs) a := by
  induction xs generalizing k B w with
  | nil =>
      simpa using hB
  | cons x xs ih =>
      let d := LineSymbol.eval e x
      let D := H.replayDup s hs k x
      let w' := w ++ [d]
      have hstep :
          MMap.comp H D B (e a) =
            wordMap H n w' a := by
        have hdup :=
          H.replayDup_step s hs e a ha k w hlen hprefix x
        have hnext :=
          H.wordMap_append_letter_succ w d a ha
        have hsame :
            D (wordMap H n w a) =
              wordMap H n (w ++ [d]) a := by
          apply Option.some.inj
          calc
            some (D (wordMap H n w a)) =
                S.succ (wordMap H n w a)
                  (H.letterCode d a ha).params
                  (H.letterCode d a ha).char := by
                    simpa [D, d] using hdup.symm
            _ = some (wordMap H n (w ++ [d]) a) := hnext
        change D (B (e a)) = wordMap H n w' a
        rw [hB, hsame]
      have hlen' :
          w'.length = s.length + 1 + (k + 1) := by
        simp [w', hlen]
        omega
      have hprefix' : s ++ [e] <+: w' :=
        hprefix.trans (w.prefix_append [d])
      change
        replayTail H s hs (k + 1) xs
          (MMap.comp H D B) (e a) =
        wordMap H n (w ++
          (LineSymbol.eval e x :: evalWord e xs)) a
      have hrec :=
        ih (k + 1) (MMap.comp H D B) w'
          hlen' hprefix' hstep
      simpa [w', d, evalWord, List.append_assoc] using hrec

/-- The final replay map sends a letter input to g_{L(e)}. -/
theorem replayMap_letter
    (H : SMTree S) {n : Nat}
    (L : StarLine (OneLevelLetter H n))
    (hs : Supports L.star)
    (e : OneLevelLetter H n)
    (a : T) (ha : LevelTree.lev a = n) :
    H.replayMap L hs (e a) =
      wordMap H n (L.eval e) a := by
  unfold replayMap
  have hstart :
      wordMap H n L.star (e a) =
        wordMap H n (L.star ++ [e]) a := by
    exact (wordMap_append_singleton_apply
      H n L.star e a).symm
  have hlen :
      (L.star ++ [e]).length = L.star.length + 1 + 0 := by
    simp
  have hpref : L.star ++ [e] <+: L.star ++ [e] :=
    List.prefix_rfl
  have h :=
    H.replayTail_letter L.star hs e a ha 0
      (afterFirstParameter L.word)
      (wordMap H n L.star)
      (L.star ++ [e])
      hlen hpref hstart
  rw [L.eval_eq_star_parameter_tail]
  simpa [List.append_assoc] using h

/-- Total M-extension representing an AM^n_2 block. -/
structure ReplayBlock
    (H : SMTree S) (n : Nat) where
  toMMap : MMap H
  fixesBelow :
    ∀ a : T, LevelTree.lev a < n → toMMap a = a

namespace ReplayBlock

instance (H : SMTree S) (n : Nat) :
    CoeFun (ReplayBlock H n) (fun _ => T → T) :=
  ⟨fun B => B.toMMap⟩

/-- The finite two-level restriction represented by the block. -/
def restrictTwo
    (H : SMTree S) (n : Nat) (B : ReplayBlock H n) :
    RestrictedMap T (n + 1) :=
  B.toMMap.restrictLe H (n + 1)

end ReplayBlock

/-- The M3 replay block fixes all levels below n. -/
theorem replayMap_eq_id_below
    (H : SMTree S) {n : Nat}
    (L : StarLine (OneLevelLetter H n))
    (hs : Supports L.star)
    {a : T} (ha : LevelTree.lev a < n) :
    H.replayMap L hs a = a := by
  let aa : {x : T // LevelTree.lev x ≤ n} :=
    ⟨a, Nat.le_of_lt ha⟩
  have hbase := H.replayMap_base L hs aa
  have hword := H.wordMap_eq_id_below n L.star ha
  exact hbase.trans hword

/-- Replay packaged as an AM^n_2 block. -/
noncomputable def replayBlock
    (H : SMTree S) {n : Nat}
    (L : StarLine (OneLevelLetter H n))
    (hs : Supports L.star) :
    ReplayBlock H n where
  toMMap := H.replayMap L hs
  fixesBelow := fun a ha => H.replayMap_eq_id_below L hs ha

/-- How a total replay block acts on the base restriction or on one
one-level letter. -/
def replayApply
    (H : SMTree S) (n : Nat)
    (B : ReplayBlock H n) :
    LineInput (OneLevelLetter H n) → RestrictedMap T n
  | .base => B.toMMap.restrictLe H n
  | .letter e =>
      (MMap.comp H B.toMMap e.toMMap).restrictLe H n

@[simp] theorem replayApply_base_apply
    (H : SMTree S) (n : Nat)
    (B : ReplayBlock H n)
    (a : {a : T // LevelTree.lev a ≤ n}) :
    replayApply H n B LineInput.base a = B a.1 := rfl

@[simp] theorem replayApply_letter_apply
    (H : SMTree S) (n : Nat)
    (B : ReplayBlock H n) (e : OneLevelLetter H n)
    (a : {a : T // LevelTree.lev a ≤ n}) :
    replayApply H n B (LineInput.letter e) a =
      B (e a.1) := rfl

/-- Concrete ReplaySystem supplied by M1--M3. -/
noncomputable def replaySystem
    (H : SMTree S) (n : Nat) :
    ReplaySystem
      (OneLevelLetter H n)
      (RestrictedMap T n)
      (ReplayBlock H n) where
  wordApprox := wordApprox H n
  apply := replayApply H n
  replay := fun L hs => H.replayBlock L hs
  replay_base := by
    intro L hs
    funext a
    exact H.replayMap_base L hs a
  replay_letter := by
    intro L hs e
    funext a
    by_cases hlt : LevelTree.lev a.1 < n
    · have he : e a.1 = a.1 :=
        e.eq_id_below H hlt
      have hbase :=
        H.replayMap_base L hs a
      have hstar :
          wordMap H n L.star a.1 = a.1 :=
        H.wordMap_eq_id_below n L.star hlt
      have heval :
          wordMap H n (L.eval e) a.1 = a.1 :=
        H.wordMap_eq_id_below n (L.eval e) hlt
      change H.replayMap L hs (e a.1) =
        wordMap H n (L.eval e) a.1
      rw [he, hbase, hstar, heval]
    · have ha : LevelTree.lev a.1 = n := by omega
      change H.replayMap L hs (e a.1) =
        wordMap H n (L.eval e) a.1
      exact H.replayMap_letter L hs e a.1 ha

/-- Lemma 3.1's Hales--Jewett step with the replay interface fully
instantiated from the tree axioms. -/
theorem oneDimensionalPigeonhole_tree
    [Fintype κ]
    (H : SMTree S) (n : Nat)
    (colour : RestrictedMap T n → κ) :
    ∃ B : ReplayBlock H n,
      ∀ x : LineInput (OneLevelLetter H n),
        colour (replayApply H n B x) =
          colour (replayApply H n B LineInput.base) := by
  exact (H.replaySystem n).oneDimensionalPigeonhole_finite colour

/-- Pairwise form of the concrete one-dimensional pigeonhole conclusion. -/
theorem oneDimensionalPigeonhole_tree_pairwise
    [Fintype κ]
    (H : SMTree S) (n : Nat)
    (colour : RestrictedMap T n → κ) :
    ∃ B : ReplayBlock H n,
      ∀ x y : LineInput (OneLevelLetter H n),
        colour (replayApply H n B x) =
          colour (replayApply H n B y) := by
  exact (H.replaySystem n).oneDimensionalPigeonhole_pairwise_finite colour

end SMTree

end SuccessorTree
