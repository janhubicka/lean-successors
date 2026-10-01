import SuccessorTree.Approximation
import SuccessorTree.Decomposition
import Mathlib.Tactic

/-!
# Recursive word approximations

This file formalizes the level bookkeeping behind the paper's maps g_w.
A finite one-level approximation is first extended tightly to the next source
level and then composed with the next one-step letter.
-/

namespace SuccessorTree

namespace ShapeMap

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

private theorem list_map_eq_self_of_mem_fix
    (p : List T) (F : ShapeMap S)
    (h : ∀ x ∈ p, F x = x) :
    p.map F = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- An M_n-style map sends a node on the boundary level n above itself. -/
theorem le_apply_of_fixesBelow
    (F : ShapeMap S) (hfix : F.FixesBelow n)
    {a : T} (ha : LevelTree.lev a = n) :
    a ≤ F a := by
  cases n with
  | zero =>
      exact F.root_le' ha
  | succ k =>
      have hapos : 0 < LevelTree.lev a := by omega
      let p := LevelTree.parent a hapos
      have hpLevel : LevelTree.lev p = k := by
        dsimp [p]
        rw [LevelTree.level_parent a hapos]
        omega
      have hpfix : F p = p := by
        apply hfix
        rw [hpLevel]
        omega
      have hparams : ∀ x ∈ S.Dp a hapos, F x = x := by
        intro x hx
        apply hfix
        have hxlt :=
          S.Dp_parameter_level_lt a hapos hx
        rw [hpLevel] at hxlt
        omega
      have hpmap : (S.Dp a hapos).map F = S.Dp a hapos :=
        list_map_eq_self_of_mem_fix (S.Dp a hapos) F hparams
      obtain ⟨d, hsucc, hda⟩ :=
        F.weak_succ' (S.succ_parent_Dp_Dc a hapos)
      have hsucc' :
          S.succ p (S.Dp a hapos) (S.Dc a hapos) = some d := by
        simpa [p, hpfix, hpmap] using hsucc
      have hcanon :
          S.succ p (S.Dp a hapos) (S.Dc a hapos) = some a := by
        simpa [p] using S.succ_parent_Dp_Dc a hapos
      have hdaEq : d = a := by
        exact Option.some.inj (hsucc'.symm.trans hcanon)
      simpa [hdaEq] using hda

end ShapeMap

namespace SMTree

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- Level maps respect composition. -/
theorem levelMap_comp
    (F G : ShapeMap S) (n : Nat) :
    H.levelMap (F.comp G) n =
      H.levelMap F (H.levelMap G n) := by
  obtain ⟨a, ha⟩ := H.level_nonempty n
  have hG :
      H.levelMap G n = LevelTree.lev (G a) := by
    simpa [ha] using H.levelMap_eq G (a := a)
  calc
    H.levelMap (F.comp G) n =
        LevelTree.lev ((F.comp G) a) := by
          simpa [ha] using H.levelMap_eq (F.comp G) (a := a)
    _ = LevelTree.lev (F (G a)) := rfl
    _ = H.levelMap F (LevelTree.lev (G a)) :=
          (H.levelMap_eq F (a := G a)).symm
    _ = H.levelMap F (H.levelMap G n) := by rw [hG]

namespace Approx

/-- The target level of the top source level of a one-level approximation. -/
noncomputable def targetLevel (g : H.Approx n n) : Nat :=
  H.levelMap (Approx.realizer H g) n

/-- The target level is independent of the chosen full realizer. -/
theorem levelMap_eq_targetLevel
    (g : H.Approx n n)
    (F : ShapeMap S)
    (happly : ∀ x : BoundedNode T n, F x.1 = g x) :
    H.levelMap F n = Approx.targetLevel H g := by
  obtain ⟨a, ha⟩ := H.level_nonempty n
  let x : BoundedNode T n := ⟨a, by simpa [ha]⟩
  have hFx : F a = g x := happly x
  have hGx : Approx.realizer H g a = g x := by
    exact Approx.realizer_apply H g x
  calc
    H.levelMap F n = LevelTree.lev (F a) := by
      simpa [ha] using H.levelMap_eq F (a := a)
    _ = LevelTree.lev (g x) := congrArg LevelTree.lev hFx
    _ = LevelTree.lev (Approx.realizer H g a) :=
      (congrArg LevelTree.lev hGx).symm
    _ = H.levelMap (Approx.realizer H g) n := by
      simpa [ha] using (H.levelMap_eq (Approx.realizer H g) (a := a)).symm
    _ = Approx.targetLevel H g := rfl

/-- A chosen tight full extension of g to source level n+1. -/
noncomputable def tightRealizer (g : H.Approx n n) : ShapeMap S :=
  Classical.choose
    (H.exists_tight_next
      (Approx.realizer H g) (Approx.realizer_mem H g) n)

theorem tightRealizer_mem (g : H.Approx n n) :
    Approx.tightRealizer H g ∈ H.M :=
  (Classical.choose_spec
    (H.exists_tight_next
      (Approx.realizer H g) (Approx.realizer_mem H g) n)).1

theorem tightRealizer_agrees (g : H.Approx n n) :
    (Approx.tightRealizer H g).AgreesThrough
      (Approx.realizer H g) n :=
  (Classical.choose_spec
    (H.exists_tight_next
      (Approx.realizer H g) (Approx.realizer_mem H g) n)).2.1

theorem tightRealizer_next (g : H.Approx n n) :
    H.levelMap (Approx.tightRealizer H g) (n + 1) =
      H.levelMap (Approx.tightRealizer H g) n + 1 :=
  (Classical.choose_spec
    (H.exists_tight_next
      (Approx.realizer H g) (Approx.realizer_mem H g) n)).2.2

theorem tightRealizer_level_n (g : H.Approx n n) :
    H.levelMap (Approx.tightRealizer H g) n =
      Approx.targetLevel H g := by
  exact (H.levelMap_eq_of_agreesThrough
    (Approx.tightRealizer_agrees H g)).trans rfl

theorem tightRealizer_fixesBelow (g : H.Approx n n) :
    (Approx.tightRealizer H g).FixesBelow n := by
  intro a ha
  have hagree :=
    Approx.tightRealizer_agrees H g a (Nat.le_of_lt ha)
  exact hagree.trans
    (Approx.realizer_fixesBelow H g a ha)

/-- One recursive letter step g -> g_e. -/
noncomputable def step
    (g : H.Approx n n) (e : H.Letter n) :
    H.Approx n n :=
  Approx.ofShapeMap H
    ((Approx.tightRealizer H g).comp (Letter.realizer H e))
    (H.comp_mem
      (Approx.tightRealizer_mem H g)
      (Letter.realizer_mem H e))
    ((Approx.tightRealizer_fixesBelow H g).comp
      (Letter.realizer_fixesBelow H e))

@[simp] theorem step_apply
    (g : H.Approx n n) (e : H.Letter n)
    (x : BoundedNode T n) :
    Approx.step H g e x =
      Approx.tightRealizer H g (Letter.realizer H e x.1) := rfl

/-- Each letter raises the image of the top source level by exactly one. -/
theorem targetLevel_step
    (g : H.Approx n n) (e : H.Letter n) :
    Approx.targetLevel H (Approx.step H g e) =
      Approx.targetLevel H g + 1 := by
  let F :=
    (Approx.tightRealizer H g).comp (Letter.realizer H e)
  have hstep :
      H.levelMap F n =
        Approx.targetLevel H (Approx.step H g e) := by
    apply Approx.levelMap_eq_targetLevel H
    intro x
    rfl
  have hcomp :
      H.levelMap F n =
        H.levelMap (Approx.tightRealizer H g)
          (H.levelMap (Letter.realizer H e) n) := by
    exact H.levelMap_comp _ _ n
  have he :
      H.levelMap (Letter.realizer H e) n = n + 1 :=
    Letter.realizer_levelMap H e
  have htight :
      H.levelMap (Approx.tightRealizer H g) (n + 1) =
        Approx.targetLevel H g + 1 := by
    rw [Approx.tightRealizer_next H g,
      Approx.tightRealizer_level_n H g]
  calc
    Approx.targetLevel H (Approx.step H g e) =
        H.levelMap F n := hstep.symm
    _ = H.levelMap (Approx.tightRealizer H g)
          (H.levelMap (Letter.realizer H e) n) := hcomp
    _ = H.levelMap (Approx.tightRealizer H g) (n + 1) := by rw [he]
    _ = Approx.targetLevel H g + 1 := htight

/-- The recursively defined approximation g_w. -/
noncomputable def word
    (w : List (H.Letter n)) : H.Approx n n :=
  w.foldl (fun g e => Approx.step H g e) (H.idApprox n)

@[simp] theorem word_nil :
    Approx.word H ([] : List (H.Letter n)) = H.idApprox n := rfl

theorem word_append
    (w : List (H.Letter n)) (e : H.Letter n) :
    Approx.word H (w ++ [e]) =
      Approx.step H (Approx.word H w) e := by
  simp [Approx.word, List.foldl_append]

theorem targetLevel_id :
    Approx.targetLevel H (H.idApprox n) = n := by
  unfold Approx.targetLevel idApprox
  have h :=
    H.levelMap_eq
      (Approx.realizer H (H.idApprox n))
      (a := Classical.choose (H.level_nonempty n))
  have ha := Classical.choose_spec (H.level_nonempty n)
  have hreal :
      Approx.realizer H (H.idApprox n)
        (Classical.choose (H.level_nonempty n)) =
        Classical.choose (H.level_nonempty n) := by
    let x : BoundedNode T n :=
      ⟨Classical.choose (H.level_nonempty n), by simpa [ha]⟩
    exact (Approx.realizer_apply H (H.idApprox n) x).trans rfl
  rw [ha] at h
  rw [hreal] at h
  simpa [ha] using h

/-- The paper's target-level formula for g_w. -/
theorem targetLevel_word
    (w : List (H.Letter n)) :
    Approx.targetLevel H (Approx.word H w) =
      n + w.length := by
  induction w using List.reverseRecOn with
  | nil =>
      simpa using Approx.targetLevel_id H (n := n)
  | append_singleton w e ih =>
      rw [Approx.word_append H w e,
        Approx.targetLevel_step H, ih]
      simp [Nat.add_assoc]

end Approx

end SMTree

end SuccessorTree
