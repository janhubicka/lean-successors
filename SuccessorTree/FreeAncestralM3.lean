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
    n (by
      change n ≤ m
      omega)

noncomputable def m3Upper
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    Node Label arity :=
  LevelTree.ancestor (⟨m, b⟩ : Node Label arity)
    (n + 1) (by
      change n + 1 ≤ m
      omega)

@[simp] theorem m3Lower_level
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    (m3Lower n m hnm b).level = n := by
  unfold m3Lower
  change
    LevelTree.lev
        (LevelTree.ancestor (⟨m, b⟩ : Node Label arity) n _) = n
  exact LevelTree.level_ancestor _ _ _

@[simp] theorem m3Upper_level
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    (m3Upper n m hnm b).level = n + 1 := by
  unfold m3Upper
  change
    LevelTree.lev
        (LevelTree.ancestor (⟨m, b⟩ : Node Label arity) (n + 1) _) =
      n + 1
  exact LevelTree.level_ancestor _ _ _

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
      have hlolev :
          LevelTree.lev (m3Lower n m hnm b) = n := by
        change (m3Lower n m hnm b).level = n
        exact m3Lower_level n m hnm b
      have huplev :
          LevelTree.lev (m3Upper n m hnm b) = n + 1 := by
        change (m3Upper n m hnm b).level = n + 1
        exact m3Upper_level n m hnm b
      rw [huplev, hlolev] at hlev
      omega
  apply LevelTree.covBy_of_le_level_succ hle
  have hlolev :
      LevelTree.lev (m3Lower n m hnm b) = n := by
    change (m3Lower n m hnm b).level = n
    exact m3Lower_level n m hnm b
  have huplev :
      LevelTree.lev (m3Upper n m hnm b) = n + 1 := by
    change (m3Upper n m hnm b).level = n + 1
    exact m3Upper_level n m hnm b
  rw [hlolev, huplev]

/-- Code replayed above a level-m node in the M3 map duplicating level n. -/
noncomputable def m3Choice
    (n m : Nat) (hnm : n < m)
    (b : History Label arity m) :
    Code Label arity m := by
  let lo := m3Lower n m hnm b
  let hi := m3Upper n m hnm b
  let hcov : lo ⋖ hi := m3Lower_covBy_upper n m hnm b
  have hlob :
      lo ≤ (⟨m, b⟩ : Node Label arity) := by
    exact LevelTree.ancestor_le _ _ _
  exact
    ⟨coverLabel hcov,
      liftParamTuple (node_level_le hlob) (coverTuple hcov)⟩

theorem m3_lower_eq
    (n m : Nat) (hnm : n < m)
    {a b : Node Label arity}
    (ha : a.level = n)
    (hb : b.level = m)
    (hab : a ≤ b) :
    a =
      m3Lower n m hnm
        (hb ▸ b.2) := by
  rcases b with ⟨bm, bh⟩
  change bm = m at hb
  subst bm
  change a = m3Lower n m hnm bh
  unfold m3Lower
  apply LevelTree.eq_ancestor_of_le hab
  · change a.level = n
    exact ha
  · change n ≤ m
    omega

theorem m3_upper_eq
    (n m : Nat) (hnm : n < m)
    {s b : Node Label arity}
    (hs : s.level = n + 1)
    (hb : b.level = m)
    (hsb : s ≤ b) :
    s =
      m3Upper n m hnm
        (hb ▸ b.2) := by
  rcases b with ⟨bm, bh⟩
  change bm = m at hb
  subst bm
  change s = m3Upper n m hnm bh
  unfold m3Upper
  apply LevelTree.eq_ancestor_of_le hsb
  · change s.level = n + 1
    exact hs
  · change n + 1 ≤ m
    omega

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
  have hcov : a ⋖ s :=
    freeSTree.covBy_of_succ_eq_some hsucc
  have hslev : s.level = n + 1 := by
    have hlev := LevelTree.covBy_level_eq hcov
    change s.level = a.level + 1 at hlev
    omega
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
  have hsuccCan :
      freeSucc (m3Lower n m hnm bh) p c =
        some (m3Upper n m hnm bh) := by
    rw [← hlo, ← hup]
    exact hsucc
  have hcanon :=
    freeSucc_s2 (freeSucc_cover hcan) hsuccCan
  have hp :
      paramNodes (m3Lower n m hnm bh) (coverTuple hcan) = p :=
    hcanon.2.1
  have hc :
      coverLabel hcan = c :=
    hcanon.2.2
  have hlob :
      m3Lower n m hnm bh ≤
        (⟨m, bh⟩ : Node Label arity) :=
    LevelTree.ancestor_le _ _ _
  have hparams :
      paramNodes (⟨m, bh⟩ : Node Label arity)
          (m3Choice n m hnm bh).params = p := by
    unfold m3Choice
    dsimp
    exact (paramNodes_lift_of_le hlob (coverTuple hcan)).trans hp
  have hlabel :
      (m3Choice n m hnm bh).label = c := by
    unfold m3Choice
    dsimp
    exact hc
  have hnew :=
    freeSucc_paramNodes
      (⟨m, bh⟩ : Node Label arity)
      (m3Choice n m hnm bh).params
      (m3Choice n m hnm bh).label
  rw [hparams, hlabel] at hnew
  rw [oneGapShapeMap_apply, gapNode_at_level]
  exact hnew


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
