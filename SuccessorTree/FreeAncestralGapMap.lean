import SuccessorTree.FreeAncestralGap
import Mathlib.Tactic

/-! # The raw one-gap map on free ancestral histories

For a fixed target gap level m, a choice function selects one immediate child
for every source node on level m.  The raw map is identity below m, takes the
chosen child at level m, and above m replays the old transition code with all
ancestral parameter levels shifted across the inserted gap.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- Level map for inserting one target gap at m. -/
def gapLevel (m n : Nat) : Nat :=
  if n < m then n else n + 1

@[simp] theorem gapLevel_of_lt
    {m n : Nat} (h : n < m) :
    gapLevel m n = n := by
  simp [gapLevel, h]

@[simp] theorem gapLevel_of_ge
    {m n : Nat} (h : m ≤ n) :
    gapLevel m n = n + 1 := by
  simp [gapLevel, Nat.not_lt.mpr h]

/-- Raw history map which inserts one level at m.

The choice function supplies the code used to move a source level-m history
to its chosen child. -/
noncomputable def gapHistory
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    (n : Nat) →
      History Label arity n →
      History Label arity (gapLevel m n)
  | 0, h => by
      have hroot : h = History.root := history_zero_unique h
      subst h
      by_cases hm : 0 < m
      · simpa [gapLevel, hm] using
          (History.root : History Label arity 0)
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        simpa [gapLevel] using
          (History.step History.root (choose History.root) :
            History Label arity 1)
  | n + 1, h => by
      cases h with
      | step p c =>
          by_cases hlt : n + 1 < m
          · simpa [gapLevel, hlt] using
              (History.step p c : History Label arity (n + 1))
          · by_cases heq : n + 1 = m
            · subst m
              simpa [gapLevel] using
                (History.step (History.step p c)
                  (choose (History.step p c)) :
                    History Label arity (n + 2))
            · have hnge : m ≤ n := by omega
              let gp0 := gapHistory m choose n p
              have gp :
                  History Label arity (n + 1) := by
                simpa [gapLevel, Nat.not_lt.mpr hnge] using gp0
              have hge : m ≤ n + 1 := by omega
              simpa [gapLevel, Nat.not_lt.mpr hge] using
                (History.step gp (shiftCode m c) :
                  History Label arity (n + 2))


theorem gapLevel_injective (m : Nat) :
    Function.Injective (gapLevel m) := by
  intro i j hij
  unfold gapLevel at hij
  by_cases hi : i < m <;> by_cases hj : j < m <;>
    simp [hi, hj] at hij ⊢ <;> omega

theorem gapHistory_injective
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    ∀ n : Nat, Function.Injective (gapHistory m choose n)
  | 0 => by
      intro x y hxy
      exact (history_zero_unique x).trans (history_zero_unique y).symm
  | n + 1 => by
      intro x y hxy
      cases x with
      | step px cx =>
          cases y with
          | step py cy =>
              by_cases hlt : n + 1 < m
              · simpa [gapHistory, hlt] using hxy
              · by_cases heq : n + 1 = m
                · subst m
                  have hpred :
                      History.step px cx =
                        History.step py cy := by
                    simpa [gapHistory] using
                      congrArg
                        (fun z =>
                          match z with
                          | History.step q _ => q)
                        hxy
                  exact hpred
                · have hnge : m ≤ n := by omega
                  have hnorm :
                      History.step
                          (gapHistory m choose n px)
                          (shiftCode m cx) =
                        History.step
                          (gapHistory m choose n py)
                          (shiftCode m cy) := by
                    simpa [gapHistory, hlt, heq, gapLevel,
                      Nat.not_lt.mpr hnge] using hxy
                  have hp :
                      gapHistory m choose n px =
                        gapHistory m choose n py := by
                    injection hnorm
                  have hc :
                      shiftCode m cx = shiftCode m cy := by
                    injection hnorm
                  have hpxy : px = py :=
                    gapHistory_injective m choose n hp
                  have hcxy : cx = cy :=
                    shiftCode_injective m hc
                  subst py
                  subst cy
                  rfl

/-- Total-node version of gapHistory. -/
noncomputable def gapNode
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    Node Label arity :=
  ⟨gapLevel m x.level, gapHistory m choose x.level x.2⟩


theorem gapNode_injective
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    Function.Injective (gapNode m choose) := by
  intro x y hxy
  have hlevels :
      gapLevel m x.level = gapLevel m y.level := by
    simpa only [gapNode_level] using congrArg Node.level hxy
  have hsrc : x.level = y.level :=
    gapLevel_injective m hlevels
  rcases x with ⟨nx, hx⟩
  rcases y with ⟨ny, hy⟩
  change nx = ny at hsrc
  subst ny
  have hhist :
      gapHistory m choose nx hx =
        gapHistory m choose nx hy := by
    simpa only [gapNode, Sigma.mk.inj_iff, heq_eq_eq,
      true_and] using hxy
  have hxyHist : hx = hy :=
    gapHistory_injective m choose nx hhist
  subst hy
  rfl

@[simp] theorem gapNode_level
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    (gapNode m choose x).level = gapLevel m x.level := rfl

theorem gapNode_level_of_lt
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level < m) :
    (gapNode m choose x).level = x.level := by
  simp [gapNode_level, gapLevel, hx]

theorem gapNode_level_of_ge
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : m ≤ x.level) :
    (gapNode m choose x).level = x.level + 1 := by
  simp [gapNode_level, gapLevel, Nat.not_lt.mpr hx]



theorem gapNode_eq_self_of_lt
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level < m) :
    gapNode m choose x = x := by
  rcases x with ⟨n, h⟩
  change n < m at hx
  cases h with
  | root =>
      simp [gapNode, gapHistory, gapLevel, hx]
  | step p c =>
      simp [gapNode, gapHistory, gapLevel, hx]

theorem gapNode_at_level
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (h : History Label arity m) :
    gapNode m choose ⟨m, h⟩ =
      child (⟨m, h⟩ : Node Label arity)
        (choose h).params (choose h).label := by
  cases m with
  | zero =>
      have hroot : h = History.root := history_zero_unique h
      subst h
      simp [gapNode, gapHistory, gapLevel, child]
  | succ n =>
      cases h with
      | step p c =>
          simp [gapNode, gapHistory, gapLevel, child]

theorem gapNode_child_of_ge
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label)
    (ha : m ≤ a.level) :
    gapNode m choose (child a t c) =
      child (gapNode m choose a)
        (shiftParamTuple m t) c := by
  rcases a with ⟨n, h⟩
  change m ≤ n at ha
  simp [gapNode, child, gapHistory, gapLevel,
    Nat.not_lt.mpr ha, Nat.not_lt.mpr (by omega : m ≤ n + 1)]


theorem gapNode_base_le_child
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    gapNode m choose a ≤
      gapNode m choose (child a t c) := by
  by_cases hlt : a.level + 1 < m
  · rw [gapNode_eq_self_of_lt m choose (by omega)]
    rw [gapNode_eq_self_of_lt m choose (by
      simpa [child_level] using hlt)]
    exact base_le_child a t c
  · by_cases heq : a.level + 1 = m
    · have haLt : a.level < m := by omega
      rw [gapNode_eq_self_of_lt m choose haLt]
      rcases a with ⟨n, h⟩
      change n + 1 = m at heq
      subst m
      change
        (⟨n, h⟩ : Node Label arity) ≤
          gapNode (n + 1) choose
            (child (⟨n, h⟩ : Node Label arity) t c)
      have hfirst :
          (⟨n, h⟩ : Node Label arity) ≤
            child (⟨n, h⟩ : Node Label arity) t c :=
        base_le_child _ _ _
      let b :=
        child (⟨n, h⟩ : Node Label arity) t c
      rcases b with ⟨k, hb⟩
      have hk : k = n + 1 := by
        simpa [b, child_level]
      subst k
      rw [gapNode_at_level]
      exact hfirst.trans (base_le_child _ _ _)
    · have hge : m ≤ a.level := by omega
      rw [gapNode_child_of_ge m choose a t c hge]
      exact base_le_child _ _ _

theorem gapNode_monotone
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x y : Node Label arity}
    (hxy : x ≤ y) :
    gapNode m choose x ≤ gapNode m choose y := by
  rcases x with ⟨l, hx⟩
  rcases y with ⟨n, hy⟩
  change Prefix hx hy at hxy
  induction hxy with
  | refl => exact le_rfl
  | @step l n hx hy hprefix c ih =>
      have hedge :
          gapNode m choose (⟨n, hy⟩ : Node Label arity) ≤
            gapNode m choose
              (⟨n + 1, History.step hy c⟩ :
                Node Label arity) := by
        exact gapNode_base_le_child
          m choose (⟨n, hy⟩ : Node Label arity)
          c.params c.label
      exact ih.trans hedge

theorem gapNode_level_eq_of_level_eq
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x y : Node Label arity}
    (hxy : x.level = y.level) :
    (gapNode m choose x).level =
      (gapNode m choose y).level := by
  simp only [gapNode_level, hxy]

theorem level_zero_eq_root
    {x : Node Label arity}
    (hx : x.level = 0) :
    x = rootNode := by
  have hroot : rootNode ≤ x := root_le x
  have hlev : rootNode.level = x.level := by
    simp [rootNode, hx, Node.level]
  exact node_eq_of_le_level_eq hroot hlev

theorem root_le_gapNode
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level = 0) :
    x ≤ gapNode m choose x := by
  have hxroot : x = rootNode :=
    level_zero_eq_root hx
  subst x
  exact root_le (gapNode m choose rootNode)

end FreeAncestral
end SuccessorTree
