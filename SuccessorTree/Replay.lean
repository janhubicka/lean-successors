import SuccessorTree.Canonical
import SuccessorTree.Pigeonhole
import Mathlib.Tactic

/-!
# Replay construction for the one-dimensional pigeonhole lemma

This file follows Section 3.1 of the successor-tree paper.  It first
formalizes the recursively defined finite maps g_w.
-/

namespace SuccessorTree

open LevelTree

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable {H : SMTree S}

namespace SMTree

/-- Level maps respect composition. -/
theorem levelMap_comp (H : SMTree S) (F G : ShapeMap S) (n : Nat) :
    H.levelMap (F.comp G) n =
      H.levelMap F (H.levelMap G n) := by
  obtain ⟨a, ha⟩ := H.level_nonempty n
  have hG :
      LevelTree.lev (G a) = H.levelMap G n := by
    simpa [ha] using (H.levelMap_eq G (a := a)).symm
  calc
    H.levelMap (F.comp G) n =
        LevelTree.lev (F (G a)) := by
      simpa [ha] using H.levelMap_eq (F.comp G) (a := a)
    _ = H.levelMap F (LevelTree.lev (G a)) :=
      (H.levelMap_eq F (a := G a)).symm
    _ = H.levelMap F (H.levelMap G n) := by rw [hG]

end SMTree

namespace Approximation

/-- Restrict a specified monoid member to a specified target cut, when its
level map is known at the source cut. -/
noncomputable def ofMemberAt
    (F : ShapeMap S) (hF : F ∈ H.M)
    (src dst : Nat)
    (hlevel : H.levelMap F src = dst) :
    Approximation H src dst where
  toFun := fun a =>
    ⟨F a.1, by
      calc
        LevelTree.lev (F a.1) =
            H.levelMap F (LevelTree.lev a.1) :=
          (H.levelMap_eq F (a := a.1)).symm
        _ ≤ H.levelMap F src :=
          (H.levelMap_strictMono F).monotone a.2
        _ = dst := hlevel⟩
  top_level := by
    intro a ha
    calc
      LevelTree.lev (F a.1) =
          H.levelMap F (LevelTree.lev a.1) :=
        (H.levelMap_eq F (a := a.1)).symm
      _ = H.levelMap F src := by rw [ha]
      _ = dst := hlevel
  extendible := ⟨F, hF, by intro a; rfl⟩

@[simp] theorem ofMemberAt_apply
    (F : ShapeMap S) (hF : F ∈ H.M)
    (src dst : Nat)
    (hlevel : H.levelMap F src = dst)
    (a : InitialSegment T src) :
    ((ofMemberAt F hF src dst hlevel) a).1 = F a.1 := rfl

/-- A canonical extension advances exactly one target level at the next source
level. -/
theorem canonicalExtension_nextLevel
    (A : Approximation H src dst) :
    H.levelMap A.canonicalExtension (src + 1) = dst + 1 := by
  have hbase :
      dst ≤ H.levelMap A.canonicalExtension src := by
    rw [A.canonicalExtension_topLevel]
  have hs :=
    H.levelMap_succ_of_tailFull
      A.canonicalExtension dst src
      A.canonicalExtension_tailFull hbase
  rw [A.canonicalExtension_topLevel] at hs
  exact hs

/-- If the finite approximation is identity below fixed, so is its canonical
extension. -/
theorem canonicalExtension_eq_id_below
    (A : Approximation H src dst)
    (hfix : A.FixesBelow fixed)
    (hfixed : fixed ≤ src)
    {a : T} (ha : LevelTree.lev a < fixed) :
    A.canonicalExtension a = a := by
  have hasrc : LevelTree.lev a ≤ src :=
    (Nat.le_of_lt ha).trans hfixed
  let x : InitialSegment T src := ⟨a, hasrc⟩
  calc
    A.canonicalExtension a = (A x).1 :=
      A.canonicalExtension_apply x
    _ = a := hfix x ha

/-- One moving level with arbitrary target cut: the extensional version of
AM^n_1. -/
structure MovingOne (H : SMTree S) (n : Nat) where
  dst : Nat
  approx : Approximation H n dst
  fixesBelow : approx.FixesBelow n

namespace MovingOne

/-- The empty word gives the identity approximation. -/
def identity (H : SMTree S) (n : Nat) : MovingOne H n where
  dst := n
  approx := Approximation.id H n
  fixesBelow := Approximation.id_fixesBelow H n

/-- A one-step Hales--Jewett alphabet letter as a general one-moving-level
approximation. -/
def ofLetter (e : OneStep H n) : MovingOne H n where
  dst := n + 1
  approx := e.toApprox
  fixesBelow := e.fixesBelow

/-- Append one alphabet letter to a word state. -/
noncomputable def step
    (X : MovingOne H n) (e : OneStep H n) :
    MovingOne H n := by
  let F := X.approx.canonicalExtension
  have hF : F ∈ H.M := X.approx.canonicalExtension_mem
  have hnext :
      H.levelMap F (n + 1) = X.dst + 1 :=
    X.approx.canonicalExtension_nextLevel
  let B : Approximation H (n + 1) (X.dst + 1) :=
    Approximation.ofMemberAt F hF (n + 1) (X.dst + 1) hnext
  let C : Approximation H n (X.dst + 1) :=
    B.comp e.toApprox
  refine ⟨X.dst + 1, C, ?_⟩
  intro a ha
  change (B (e.toApprox a)).1 = a.1
  change F (e.toApprox a).1 = a.1
  have he : (e.toApprox a).1 = a.1 :=
    e.fixesBelow a ha
  rw [he]
  exact X.approx.canonicalExtension_eq_id_below
    X.fixesBelow le_rfl ha

@[simp] theorem step_dst
    (X : MovingOne H n) (e : OneStep H n) :
    (X.step e).dst = X.dst + 1 := by
  rfl

/-- Run a word from an existing one-moving-level state. -/
noncomputable def run
    (X : MovingOne H n) : List (OneStep H n) → MovingOne H n
  | [] => X
  | e :: w => run (X.step e) w

@[simp] theorem run_nil (X : MovingOne H n) :
    X.run [] = X := rfl

@[simp] theorem run_cons
    (X : MovingOne H n) (e : OneStep H n) (w : List (OneStep H n)) :
    X.run (e :: w) = (X.step e).run w := rfl

theorem run_append
    (X : MovingOne H n)
    (u v : List (OneStep H n)) :
    X.run (u ++ v) = (X.run u).run v := by
  induction u generalizing X with
  | nil => rfl
  | cons e u ih =>
      simp only [List.cons_append, run_cons]
      exact ih (X.step e)

theorem run_dst
    (X : MovingOne H n) :
    ∀ w : List (OneStep H n),
      (X.run w).dst = X.dst + w.length := by
  intro w
  induction w generalizing X with
  | nil => simp
  | cons e w ih =>
      rw [run_cons, ih]
      simp
      omega

/-- The paper's recursively defined g_w. -/
noncomputable def wordApprox
    (H : SMTree S) (n : Nat)
    (w : List (OneStep H n)) : MovingOne H n :=
  (identity H n).run w

@[simp] theorem wordApprox_dst
    (H : SMTree S) (n : Nat)
    (w : List (OneStep H n)) :
    (wordApprox H n w).dst = n + w.length := by
  unfold wordApprox
  rw [run_dst]
  rfl

theorem wordApprox_append
    (H : SMTree S) (n : Nat)
    (u v : List (OneStep H n)) :
    wordApprox H n (u ++ v) =
      (wordApprox H n u).run v := by
  exact run_append (identity H n) u v

theorem wordApprox_snoc
    (H : SMTree S) (n : Nat)
    (u : List (OneStep H n)) (e : OneStep H n) :
    wordApprox H n (u ++ [e]) =
      (wordApprox H n u).step e := by
  rw [wordApprox_append]
  rfl

end MovingOne

/-- A one-step alphabet letter places each top-level source node below its
image. -/
theorem OneStep.le_apply
    (e : OneStep H n)
    (a : InitialSegment T n)
    (ha : LevelTree.lev a.1 = n) :
    a.1 ≤ (e.toApprox a).1 := by
  let F := e.toApprox.someExtension
  have hFa : F a.1 = (e.toApprox a).1 :=
    e.toApprox.someExtension_apply a
  cases n with
  | zero =>
      have hroot : a.1 ≤ F a.1 :=
        F.root_le' (by simpa using ha)
      simpa [hFa] using hroot
  | succ k =>
      have hk_le : k ≤ LevelTree.lev a.1 := by omega
      let x := LevelTree.ancestor a.1 k hk_le
      have hxa : x ≤ a.1 :=
        LevelTree.ancestor_le a.1 k hk_le
      have hxlev : LevelTree.lev x = k :=
        LevelTree.level_ancestor a.1 k hk_le
      have hcover : x ⋖ a.1 := by
        apply LevelTree.covBy_of_le_level_succ hxa
        omega
      obtain ⟨p, c, hsucc⟩ := S.s3 hcover
      let xs : InitialSegment T (k + 1) :=
        ⟨x, by simpa [hxlev]⟩
      have hxfixFinite : (e.toApprox xs).1 = x := by
        apply e.fixesBelow xs
        omega
      have hFx : F x = x := by
        calc
          F x = (e.toApprox xs).1 :=
            e.toApprox.someExtension_apply xs
          _ = x := hxfixFinite
      have hpfix : ∀ y ∈ p, F y = y := by
        intro y hy
        have hylt := S.parameter_level_lt hsucc hy
        let ys : InitialSegment T (k + 1) :=
          ⟨y, by omega⟩
        calc
          F y = (e.toApprox ys).1 :=
            e.toApprox.someExtension_apply ys
          _ = y := e.fixesBelow ys (by omega)
      have hpmap : p.map F = p := by
        induction p with
        | nil => rfl
        | cons y ys ih =>
            have hy : F y = y := hpfix y (by simp)
            have hys : ∀ z ∈ ys, F z = z := by
              intro z hz
              exact hpfix z (by simp [hz])
            simp only [List.map_cons]
            rw [hy, ih hys]
      obtain ⟨d, hd, hda⟩ := F.weak_succ' hsucc
      have hd' : S.succ x p c = some d := by
        simpa [hFx, hpmap] using hd
      have hdeq : d = a.1 := by
        exact Option.some.inj (hd'.symm.trans hsucc)
      subst d
      rw [hFa] at hda
      exact hda

/-- A one-step alphabet letter has an S-decomposition over every top-level
source node. -/
theorem OneStep.exists_successor
    (e : OneStep H n)
    (a : InitialSegment T n)
    (ha : LevelTree.lev a.1 = n) :
    ∃ p : List T, ∃ c : Label,
      S.succ a.1 p c = some (e.toApprox a).1 := by
  have hle := e.le_apply a ha
  have htop :
      LevelTree.lev (e.toApprox a).1 = n + 1 :=
    e.toApprox.top_level a ha
  have hcover : a.1 ⋖ (e.toApprox a).1 := by
    apply LevelTree.covBy_of_le_level_succ hle
    omega
  exact S.s3 hcover

private theorem replay_map_eq_self
    (p : List T) (F : ShapeMap S)
    (h : ∀ x ∈ p, F x = x) :
    p.map F = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

/-- Pointwise form of the recursive equation
g_(u appended e)(a) = g_u^+(e(a)). -/
theorem MovingOne.step_apply
    (X : MovingOne H n) (e : OneStep H n)
    (a : InitialSegment T n) :
    ((X.step e).approx a).1 =
      X.approx.canonicalExtension (e.toApprox a).1 := by
  rfl

/-- On a top source node, appending a letter transports its successor
decomposition through the preceding canonical extension. -/
theorem MovingOne.step_successor
    (X : MovingOne H n) (e : OneStep H n)
    (a : InitialSegment T n)
    (ha : LevelTree.lev a.1 = n)
    {p : List T} {c : Label}
    (hsucc : S.succ a.1 p c = some (e.toApprox a).1) :
    S.succ (X.approx a).1 p c =
      some ((X.step e).approx a).1 := by
  let F := X.approx.canonicalExtension
  have hpfix : ∀ y ∈ p, F y = y := by
    intro y hy
    have hylt := S.parameter_level_lt hsucc hy
    exact X.approx.canonicalExtension_eq_id_below
      X.fixesBelow le_rfl (by omega)
  have hpmap : p.map F = p :=
    replay_map_eq_self p F hpfix
  have hlevels :
      H.levelMap F (LevelTree.lev (e.toApprox a).1) =
        H.levelMap F (LevelTree.lev a.1) + 1 := by
    have heTop :
        LevelTree.lev (e.toApprox a).1 = n + 1 :=
      e.toApprox.top_level a ha
    rw [ha, heTop]
    exact X.approx.canonicalExtension_nextLevel
  have hexact :=
    H.succ_eq_of_consecutive_levels F hsucc hlevels
  have hFa :
      F a.1 = (X.approx a).1 :=
    X.approx.canonicalExtension_apply a
  rw [hFa, hpmap] at hexact
  rw [MovingOne.step_apply]
  exact hexact

/-- Extensional equality for one-moving-level approximations. -/
@[ext] theorem MovingOne.ext
    {X Y : MovingOne H n}
    (h : ∀ a : InitialSegment T n,
      (X.approx a).1 = (Y.approx a).1) :
    X = Y := by
  obtain ⟨top, htop⟩ := H.level_nonempty n
  let a : InitialSegment T n := ⟨top, by omega⟩
  have hdst : X.dst = Y.dst := by
    calc
      X.dst = LevelTree.lev (X.approx a).1 :=
        (X.approx.top_level a htop).symm
      _ = LevelTree.lev (Y.approx a).1 := by
        rw [h a]
      _ = Y.dst := Y.approx.top_level a htop
  cases X with
  | mk dx AX hX =>
      cases Y with
      | mk dy AY hY =>
          dsimp at hdst h ⊢
          subst dy
          have hA : AX = AY := by
            apply Approximation.ext
            exact h
          subst AY
          rfl

/-- Two moving source levels, the extensional version of AM^n_2. -/
structure MovingTwo (H : SMTree S) (n : Nat) where
  dst : Nat
  approx : Approximation H (n + 1) dst
  fixesBelow : approx.FixesBelow n

namespace MovingTwo

/-- The first shape-preserving block after the first parameter of a line is
the canonical extension of its star-prefix word, restricted through n+1. -/
noncomputable def fromOne
    (X : MovingOne H n) : MovingTwo H n := by
  let F := X.approx.canonicalExtension
  have hF : F ∈ H.M := X.approx.canonicalExtension_mem
  have hnext :
      H.levelMap F (n + 1) = X.dst + 1 :=
    X.approx.canonicalExtension_nextLevel
  let B : Approximation H (n + 1) (X.dst + 1) :=
    Approximation.ofMemberAt F hF (n + 1) (X.dst + 1) hnext
  refine ⟨X.dst + 1, B, ?_⟩
  intro a ha
  change F a.1 = a.1
  exact X.approx.canonicalExtension_eq_id_below
    X.fixesBelow le_rfl ha

@[simp] theorem fromOne_dst
    (X : MovingOne H n) :
    (fromOne X).dst = X.dst + 1 := rfl

/-- Restriction of a two-moving-level block to its lower moving level. -/
noncomputable def base
    (B : MovingTwo H n) : MovingOne H n := by
  let F := B.approx.someExtension
  let d := H.levelMap F n
  let A : Approximation H n d :=
    Approximation.ofMemberAt F B.approx.someExtension_mem n d rfl
  refine ⟨d, A, ?_⟩
  intro a ha
  change F a.1 = a.1
  let au : InitialSegment T (n + 1) :=
    InitialSegment.castLE (Nat.le_succ n) a
  calc
    F a.1 = (B.approx au).1 :=
      B.approx.someExtension_apply au
    _ = a.1 := B.fixesBelow au ha

/-- Compose a two-moving-level block with a one-step line letter. -/
noncomputable def letter
    (B : MovingTwo H n) (e : OneStep H n) :
    MovingOne H n := by
  let C : Approximation H n B.dst :=
    B.approx.comp e.toApprox
  refine ⟨B.dst, C, ?_⟩
  intro a ha
  change (B.approx (e.toApprox a)).1 = a.1
  let au : InitialSegment T (n + 1) :=
    InitialSegment.castLE (Nat.le_succ n) a
  have he : e.toApprox a = au := by
    apply Subtype.ext
    exact e.fixesBelow a ha
  rw [he]
  exact B.fixesBelow au ha

/-- Action of a two-moving-level block on the finite line L_n. -/
noncomputable def apply
    (B : MovingTwo H n) :
    LineInput (OneStep H n) → MovingOne H n
  | .base => B.base
  | .letter e => B.letter e

@[simp] theorem apply_base
    (B : MovingTwo H n) :
    B.apply LineInput.base = B.base := rfl

@[simp] theorem apply_letter
    (B : MovingTwo H n) (e : OneStep H n) :
    B.apply (LineInput.letter e) = B.letter e := rfl

/-- Pointwise restriction identity for the base action. -/
theorem base_apply
    (B : MovingTwo H n) (a : InitialSegment T n) :
    ((B.base).approx a).1 =
      (B.approx (InitialSegment.castLE (Nat.le_succ n) a)).1 := by
  change B.approx.someExtension a.1 =
    (B.approx (InitialSegment.castLE (Nat.le_succ n) a)).1
  exact B.approx.someExtension_apply
    (InitialSegment.castLE (Nat.le_succ n) a)

/-- Pointwise formula for the letter action. -/
@[simp] theorem letter_apply
    (B : MovingTwo H n) (e : OneStep H n)
    (a : InitialSegment T n) :
    ((B.letter e).approx a).1 =
      (B.approx (e.toApprox a)).1 := rfl

end MovingTwo

end Approximation

namespace SMTree

/-- A fixed choice of the M3 duplication map. -/
noncomputable def duplicator
    (H : SMTree S) (source target : Nat)
    (h : source < target) : ShapeMap S :=
  Classical.choose (H.m3 source target h)

theorem duplicator_mem
    (H : SMTree S) (source target : Nat)
    (h : source < target) :
    H.duplicator source target h ∈ H.M :=
  (Classical.choose_spec (H.m3 source target h)).1

theorem duplicator_skipsOnly
    (H : SMTree S) (source target : Nat)
    (h : source < target) :
    (H.duplicator source target h).SkipsOnly target :=
  (Classical.choose_spec (H.m3 source target h)).2.1

theorem duplicator_spec
    (H : SMTree S) (source target : Nat)
    (h : source < target)
    (a b : T) (p : List T) (c : Label) (s : T)
    (ha : LevelTree.lev a = source)
    (hb : LevelTree.lev b = target)
    (hsucc : S.succ a p c = some s)
    (hsb : s ≤ b) :
    S.succ b p c =
      some (H.duplicator source target h b) := by
  exact (Classical.choose_spec (H.m3 source target h)).2.2
    a b p c s ha hb hsucc hsb

end SMTree

namespace Approximation

end Approximation

end SuccessorTree
