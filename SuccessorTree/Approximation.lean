import SuccessorTree.Monoid
import Mathlib.Data.Fintype.Pi
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

/-- M-maps are determined by their underlying shape maps. -/
theorem ext_map {H : SMTree S} {F G : MMap H} (h : F.map = G.map) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Pointwise extensionality for M-maps. -/
theorem ext_apply {H : SMTree S} {F G : MMap H}
    (h : ∀ a : T, F a = G a) : F = G :=
  ext_map (ShapeMap.ext_apply h)

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

/-- One-level letters are determined by their underlying M-maps. -/
theorem ext_toMMap {H : SMTree S} {n : Nat} {e f : OneLevelLetter H n}
    (h : e.toMMap = f.toMMap) : e = f := by
  cases e
  cases f
  cases h
  rfl

end OneLevelLetter

/-- Successor decomposition data for a fixed edge a <. b. -/
structure SuccCode (S : STree T Label) (a b : T) where
  params : List T
  char : Label
  succ_eq : S.succ a params char = some b

/-- S3 supplies successor code for every cover. -/
noncomputable def succCodeOfCovBy (S : STree T Label)
    {a b : T} (h : a ⋖ b) : SuccCode S a b :=
  let p := Classical.choose (S.s3 h)
  let hc := Classical.choose_spec (S.s3 h)
  let c := Classical.choose hc
  ⟨p, c, Classical.choose_spec hc⟩

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

/-- Nodes on one fixed level, packaged as a finite type. -/
abbrev LevelNode (T : Type u) [PartialOrder T] [LevelTree T] (n : Nat) :=
  {a : T // LevelTree.lev a = n}

noncomputable instance levelNodeFintype
    (T : Type u) [PartialOrder T] [LevelTree T] (n : Nat) :
    Fintype (LevelNode T n) :=
  Set.Finite.fintype (LevelTree.level_finite n)

/-- Action of a one-level letter on the skipped source level. -/
def OneLevelLetter.levelImage
    (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) :
    LevelNode T n → LevelNode T (n + 1) :=
  fun a => ⟨e a.1, e.level_succ_at H a.2⟩

/-- One-level letters are determined by their action on level n. -/
theorem OneLevelLetter.levelImage_injective
    (H : SMTree S) (n : Nat) :
    Function.Injective
      (fun e : OneLevelLetter H n => e.levelImage H) := by
  intro e f hef
  have hpoint :
      ∀ a : LevelNode T n, e a.1 = f a.1 := by
    intro a
    exact congrArg Subtype.val (congrFun hef a)
  have himage :
      Set.range
          (fun a : {a : T // LevelTree.lev a = n} => e.toMMap.map a.1) =
        Set.range
          (fun a : {a : T // LevelTree.lev a = n} => f.toMMap.map a.1) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hpoint a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hpoint a⟩
  have hfun :
      e.toMMap.map.toFun = f.toMMap.map.toFun :=
    H.eq_of_skipsOnly_levelImage
      e.toMMap.map f.toMMap.map n e.skips f.skips himage
  apply OneLevelLetter.ext_toMMap
  apply MMap.ext_map
  exact ShapeMap.ext_toFun hfun

/-- The Hales--Jewett alphabet at a fixed level is finite. -/
noncomputable instance oneLevelLetterFintype
    (H : SMTree S) (n : Nat) :
    Fintype (OneLevelLetter H n) := by
  letI : Fintype (LevelNode T n) := levelNodeFintype T n
  letI : Fintype (LevelNode T (n + 1)) := levelNodeFintype T (n + 1)
  letI : DecidableEq (LevelNode T n) := Classical.decEq _
  letI : DecidableEq (LevelNode T (n + 1)) := Classical.decEq _
  exact Fintype.ofInjective
    (fun e : OneLevelLetter H n => e.levelImage H)
    (OneLevelLetter.levelImage_injective H n)

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

/-- On every input at or above n, each letter raises the level once. -/
theorem level_wordMap_of_ge (H : SMTree S) (n : Nat)
    (w : List (OneLevelLetter H n)) {a : T}
    (ha : n ≤ LevelTree.lev a) :
    LevelTree.lev (wordMap H n w a) =
      LevelTree.lev a + w.length := by
  induction w with
  | nil => simp
  | cons e w ih =>
      rw [wordMap_cons_apply, e.level_apply H, ih]
      have hnot : ¬ LevelTree.lev a + w.length < n := by omega
      simp [hnot]
      omega

/-- A letter edge has parameters strictly below the fixed level n. -/
theorem letterCode_params_below
    (H : SMTree S) {n : Nat}
    (e : OneLevelLetter H n) (a : T)
    (ha : LevelTree.lev a = n)
    {x : T} (hx : x ∈ (H.letterCode e a ha).params) :
    LevelTree.lev x < n := by
  have h := S.parameter_level_lt (H.letterCode e a ha).succ_eq hx
  simpa [ha] using h

private theorem list_map_eq_self_of_fixed
    {α : Type u} (p : List α) (f : α → α)
    (h : ∀ x ∈ p, f x = x) :
    p.map f = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = x := h x (List.mem_cons_self)
      simp only [List.map_cons]
      rw [hx, ih]

/-- Every word map fixes the parameter list of a one-level letter edge. -/
theorem map_letterCode_params_eq
    (H : SMTree S) {n : Nat}
    (w : List (OneLevelLetter H n))
    (e : OneLevelLetter H n) (a : T)
    (ha : LevelTree.lev a = n) :
    (H.letterCode e a ha).params.map (wordMap H n w) =
      (H.letterCode e a ha).params := by
  let p := (H.letterCode e a ha).params
  have hfix : ∀ x ∈ p, wordMap H n w x = x := by
    intro x hx
    apply wordMap_eq_id_below H n w
    exact H.letterCode_params_below e a ha hx
  change p.map (wordMap H n w) = p
  exact list_map_eq_self_of_fixed p (wordMap H n w) hfix

/-- Appending one letter gives exactly the corresponding successor edge after
the preceding word has been applied. -/
theorem wordMap_append_letter_succ
    (H : SMTree S) {n : Nat}
    (w : List (OneLevelLetter H n))
    (e : OneLevelLetter H n) (a : T)
    (ha : LevelTree.lev a = n) :
    S.succ (wordMap H n w a)
        (H.letterCode e a ha).params
        (H.letterCode e a ha).char =
      some (wordMap H n (w ++ [e]) a) := by
  have hedge := (H.letterCode e a ha).succ_eq
  obtain ⟨d, hd, hdb⟩ := (wordMap H n w).map.weak_succ' hedge
  have hparams := H.map_letterCode_params_eq w e a ha
  rw [hparams] at hd
  have hbase :
      LevelTree.lev (wordMap H n w a) = n + w.length :=
    H.level_wordMap_at n w ha
  have hdlev :
      LevelTree.lev d = LevelTree.lev (wordMap H n w a) + 1 :=
    LevelTree.covBy_level_eq (S.covBy_of_succ_eq_some hd)
  have healvl : LevelTree.lev (e a) = n + 1 :=
    e.level_succ_at H ha
  have htarget :
      LevelTree.lev (wordMap H n w (e a)) =
        LevelTree.lev (e a) + w.length :=
    H.level_wordMap_of_ge n w (a := e a) (by omega)
  have hsame :
      LevelTree.lev d = LevelTree.lev (wordMap H n w (e a)) := by
    omega
  have heq : d = wordMap H n w (e a) :=
    LevelTree.same_level_of_le hdb hsame
  rw [wordMap_append_singleton_apply]
  simpa [heq] using hd

/-- Consecutive word prefixes form a cover on every level-n node. -/
theorem wordMap_covBy_append_letter
    (H : SMTree S) {n : Nat}
    (w : List (OneLevelLetter H n))
    (e : OneLevelLetter H n) (a : T)
    (ha : LevelTree.lev a = n) :
    wordMap H n w a ⋖ wordMap H n (w ++ [e]) a :=
  S.covBy_of_succ_eq_some
    (H.wordMap_append_letter_succ w e a ha)

/-- A word prefix maps a level-n node below every longer extension. -/
theorem wordMap_le_append
    (H : SMTree S) {n : Nat}
    (u v : List (OneLevelLetter H n))
    (a : T) (ha : LevelTree.lev a = n) :
    wordMap H n u a ≤ wordMap H n (u ++ v) a := by
  induction v using List.reverseRecOn with
  | nil =>
      simp
  | append_singleton v e ih =>
      rw [← List.append_assoc]
      exact ih.trans
        (H.wordMap_covBy_append_letter (u ++ v) e a ha).le

/-- If a letter occurs after prefix u in a larger word, its successor edge
lies below the endpoint of the whole word. -/
theorem wordMap_append_letter_le
    (H : SMTree S) {n : Nat}
    (u v : List (OneLevelLetter H n))
    (e : OneLevelLetter H n)
    (a : T) (ha : LevelTree.lev a = n) :
    wordMap H n (u ++ [e]) a ≤
      wordMap H n (u ++ e :: v) a := by
  have h :=
    H.wordMap_le_append (u ++ [e]) v a ha
  simpa [List.append_assoc] using h

/-- Split a list at a chosen occurrence. -/
theorem exists_split_of_mem {α : Type u} {x : α} {s : List α}
    (hx : x ∈ s) :
    ∃ u v : List α, s = u ++ x :: v := by
  induction s with
  | nil =>
      simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨u, v, huv⟩ := ih hx
        refine ⟨y :: u, v, ?_⟩
        simp [huv]

/-- Word-map endpoints are monotone under word-prefix. -/
theorem wordMap_le_of_prefix
    (H : SMTree S) {n : Nat}
    {u v : List (OneLevelLetter H n)}
    (huv : u <+: v)
    (a : T) (ha : LevelTree.lev a = n) :
    wordMap H n u a ≤ wordMap H n v a := by
  rcases huv with ⟨t, rfl⟩
  exact H.wordMap_le_append u t a ha

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
