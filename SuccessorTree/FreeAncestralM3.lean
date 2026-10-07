import SuccessorTree.FreeAncestralCover
import SuccessorTree.FreeAncestralMonoid
import Mathlib.Tactic

/-! # M3 replay choice for the free ancestral tree -/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

noncomputable def m3Lower
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    Node Label arity :=
  LevelTree.ancestor (⟨m, b⟩ : Node Label arity)
    n (Nat.le_of_lt hnm)

noncomputable def m3Upper
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    Node Label arity :=
  LevelTree.ancestor (⟨m, b⟩ : Node Label arity)
    (n + 1) (by omega)

@[simp] theorem m3Lower_level
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    (m3Lower n m hnm b).level = n := by
  simp [m3Lower, LevelTree.level_ancestor]

@[simp] theorem m3Upper_level
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    (m3Upper n m hnm b).level = n + 1 := by
  simp [m3Upper, LevelTree.level_ancestor]

theorem m3Lower_covBy_upper
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    m3Lower n m hnm b ⋖ m3Upper n m hnm b := by
  have hlo :
      m3Lower n m hnm b ≤
        (⟨m, b⟩ : Node Label arity) :=
    LevelTree.ancestor_le _ _ _
  have hup :
      m3Upper n m hnm b ≤
        (⟨m, b⟩ : Node Label arity) :=
    LevelTree.ancestor_le _ _ _
  have hle :
      m3Lower n m hnm b ≤
        m3Upper n m hnm b := by
    rcases LevelTree.comparable_below hlo hup with h | h
    · exact h
    · have hlev := LevelTree.level_le_of_le h
      simp at hlev
  apply LevelTree.covBy_of_le_level_succ hle
  simp

/-- Code replayed above a level-m node in the M3 map duplicating level n. -/
noncomputable def m3Choice
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    Code Label arity m :=
  liftCode (Nat.le_of_lt hnm)
    (coverCode (m3Lower_covBy_upper n m hnm b))

theorem m3_lower_eq
    (n m : Nat) (hnm : n < m)
    {a b : Node Label arity}
    (ha : a.level = n)
    (hb : b.level = m)
    (hab : a ≤ b) :
    a =
      m3Lower n m hnm
        (hb ▸ b.2) := by
  subst m
  have h :=
    LevelTree.eq_ancestor_of_le hab ha
      (Nat.le_of_lt hnm)
  simpa [m3Lower] using h

theorem m3_upper_eq
    (n m : Nat) (hnm : n < m)
    {s b : Node Label arity}
    (hs : s.level = n + 1)
    (hb : b.level = m)
    (hsb : s ≤ b) :
    s =
      m3Upper n m hnm
        (hb ▸ b.2) := by
  subst m
  have h :=
    LevelTree.eq_ancestor_of_le hsb hs
      (by omega)
  simpa [m3Upper] using h

theorem m3_replay
    (n m : Nat) (hnm : n < m)
    {a b s : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (ha : a.level = n)
    (hb : b.level = m)
    (hsucc : freeSucc a p c = some s)
    (hsb : s ≤ b) :
    freeSucc b p c =
      some
        (oneGapShapeMap m (m3Choice n m hnm) b) := by
  obtain ⟨t, htp, hseq⟩ :=
    freeSucc_eq_some_data hsucc
  have hcov : a ⋖ s :=
    freeSTree.covBy_of_succ_eq_some hsucc
  have hslev : s.level = n + 1 := by
    rw [LevelTree.covBy_level_eq hcov, ha]
  have hab : a ≤ b :=
    hcov.le.trans hsb
  rcases b with ⟨bm, bh⟩
  change bm = m at hb
  subst bm
  have hlo :
      a = m3Lower n m hnm bh :=
    m3_lower_eq n m hnm ha rfl hab
  have hup :
      s = m3Upper n m hnm bh :=
    m3_upper_eq n m hnm hslev rfl hsb
  let hcan := m3Lower_covBy_upper n m hnm bh
  have hcanEq : hcan = hcov := by
    apply Subsingleton.elim
  have hdata :
      coverTuple hcan = t ∧
        coverLabel hcan = c := by
    apply cover_data_eq_of_child hcan t c
    rw [← hlo, ← hup]
    exact hseq
  have hchoice :
      m3Choice n m hnm bh =
        liftCode (Nat.le_of_lt hnm)
          (⟨c, t⟩ : Code Label arity n) := by
    unfold m3Choice coverCode
    rw [hdata.1, hdata.2]
  have hparams :
      paramNodes (⟨m, bh⟩ : Node Label arity)
          (liftParamTuple
            (show a.level ≤ (⟨m, bh⟩ : Node Label arity).level by
              simpa [ha] using Nat.le_of_lt hnm)
            t) =
        p := by
    have hlift :=
      paramNodes_lift_of_le
        (a := a) (b := (⟨m, bh⟩ : Node Label arity))
        hab t
    exact hlift.trans htp
  have hnew :=
    freeSucc_paramNodes
      (⟨m, bh⟩ : Node Label arity)
      (liftParamTuple
        (show a.level ≤ (⟨m, bh⟩ : Node Label arity).level by
          simpa [ha] using Nat.le_of_lt hnm)
        t)
      c
  rw [hparams] at hnew
  rw [oneGapShapeMap_apply, gapNode_at_level, hchoice]
  simpa [liftCode, ha] using hnew


variable [Nonempty Label]

theorem free_m3_exists
    (n m : Nat) (hnm : n < m) :
    ∃ D : ShapeMap (freeSTree (Label := Label) (arity := arity)),
      D.SkipsOnly m ∧
      ∀ (a b : Node Label arity)
        (p : List (Node Label arity))
        (c : Label) (s : Node Label arity),
        a.level = n →
        b.level = m →
        freeSucc a p c = some s →
        s ≤ b →
        freeSucc b p c = some (D b) := by
  let D :
      ShapeMap (freeSTree (Label := Label) (arity := arity)) :=
    oneGapShapeMap m (m3Choice n m hnm)
  refine ⟨D, ?_, ?_⟩
  · exact oneGapShapeMap_skipsOnly
      m (m3Choice n m hnm)
  · intro a b p c s ha hb hsucc hsb
    exact m3_replay n m hnm ha hb hsucc hsb

end FreeAncestral
end SuccessorTree
