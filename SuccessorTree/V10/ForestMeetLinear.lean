import SuccessorTree.Tree
import SuccessorTree.Envelope
import Mathlib.Tactic

/-!
# Sharp finite forest meet-closure bound: 2N

Proposition 6.44 of the successor v10 manuscript uses the sharp
estimate for a forest generated under componentwise meets by N
original nodes. The present file proves it directly from LevelTree,
without treating unrelated root components as having a meet.

When one original u is adjoined to V, select the highest old
cross-meet y = meet(u,a0) along u's predecessor chain.
A lower cross-meet x = meet(u,a) is exactly meet(a,a0) of
two older originals; it is not a new branch point. Thus the
new finite meet set adds at most two nodes: u and y.

Induction yields the sharp upper bound 2 * |V|. The next v10
application must show that the final concrete Kpt closure
lies inside the finite set of originals and their pair-meets.
-/

namespace SuccessorTree.V10

universe u

variable {T : Type u} [PartialOrder T] [LevelTree T]

private theorem forest_meet_comm_of_related {a b : T}
    (h : SMTree.Envelope.SameComponent a b) :
    LevelTree.meet a b = LevelTree.meet b a := by
  have hr : SMTree.Envelope.SameComponent b a := by
    obtain ⟨c,hca,hcb⟩ := h
    exact ⟨c,hcb,hca⟩
  apply le_antisymm
  · exact LevelTree.le_meet
      (LevelTree.meet_le_right h) (LevelTree.meet_le_left h)
  · exact LevelTree.le_meet
      (LevelTree.meet_le_right hr) (LevelTree.meet_le_left hr)

private theorem forest_meet_self (a : T) :
    LevelTree.meet a a = a := by
  apply le_antisymm
  · exact LevelTree.meet_le_left ⟨a,le_rfl,le_rfl⟩
  · exact LevelTree.le_meet le_rfl le_rfl

/-- Original nodes plus all defined componentwise pair meets. -/
noncomputable def forestFiniteMeetNodes (V : Finset T) : Finset T := by
  classical
  exact V ∪
    (((V.product V).filter
      (fun ab : T × T =>
        SMTree.Envelope.SameComponent ab.1 ab.2)).image
      (fun ab : T × T => LevelTree.meet ab.1 ab.2))

theorem forestFiniteMeetNodes_mem_iff
    (V : Finset T) (x : T) :
    x ∈ forestFiniteMeetNodes V ↔
      x ∈ V ∨
        ∃ a : T, a ∈ V ∧ ∃ b : T, b ∈ V ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.meet a b = x := by
  classical
  unfold forestFiniteMeetNodes
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hv | hm
    · exact Or.inl hv
    · obtain ⟨⟨a,b⟩,hp,heq⟩ := Finset.mem_image.mp hm
      obtain ⟨hprod,hrelated⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha,hb⟩ := Finset.mem_product.mp hprod
      exact Or.inr ⟨a,ha,b,hb,hrelated,heq⟩
  · intro h
    apply Finset.mem_union.mpr
    rcases h with hv | ⟨a,ha,b,hb,hrelated,heq⟩
    · exact Or.inl hv
    · apply Or.inr
      apply Finset.mem_image.mpr
      exact ⟨(a,b),
        Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hrelated⟩,heq⟩

/-- Two new cross-meets at different heights determine a meet
of two old originals, namely the lower cross-meet. -/
private theorem forest_strict_cross_meet_is_old
    {a b w : T}
    (hwa : SMTree.Envelope.SameComponent w a)
    (hwb : SMTree.Envelope.SameComponent w b)
    (hlt : LevelTree.meet w a < LevelTree.meet w b) :
    LevelTree.meet w a = LevelTree.meet a b := by
  let x := LevelTree.meet w a
  let y := LevelTree.meet w b
  have hxa : x ≤ a := LevelTree.meet_le_right hwa
  have hxb : x ≤ b := hlt.le.trans (LevelTree.meet_le_right hwb)
  have hab : SMTree.Envelope.SameComponent a b := ⟨x,hxa,hxb⟩
  have hxz : x ≤ LevelTree.meet a b := LevelTree.le_meet hxa hxb
  have hza : LevelTree.meet a b ≤ a := LevelTree.meet_le_left hab
  have hzb : LevelTree.meet a b ≤ b := LevelTree.meet_le_right hab
  have hyb : y ≤ b := LevelTree.meet_le_right hwb
  rcases LevelTree.comparable_below hzb hyb with hzy | hyz
  · have hzw : LevelTree.meet a b ≤ w :=
      hzy.trans (LevelTree.meet_le_left hwb)
    exact le_antisymm hxz (LevelTree.le_meet hzw hza)
  · have hya : y ≤ a := hyz.trans hza
    have hyx : y ≤ x :=
      LevelTree.le_meet (LevelTree.meet_le_left hwb) hya
    exact False.elim ((not_le_of_gt hlt) hyx)

/-- If all compatible new cross-meets are either old or one
fixed new branch point y, inserting w adds only w and y. -/
private theorem forestFiniteMeetNodes_insert_subset_of_cross
    (w : T) (V : Finset T) (y : T)
    (hcross : ∀ a : T, a ∈ V →
      SMTree.Envelope.SameComponent w a →
      LevelTree.meet w a ∈ forestFiniteMeetNodes V ∪ {y}) :
    forestFiniteMeetNodes (insert w V) ⊆
      (forestFiniteMeetNodes V ∪ {w}) ∪ {y} := by
  classical
  intro x hx
  have hMem : (x ∈ forestFiniteMeetNodes V ∨ x = w) ∨ x = y := by
    rcases (forestFiniteMeetNodes_mem_iff (insert w V) x).mp hx with
      hOld | ⟨a,ha,b,hb,hRel,hEq⟩
    · rcases Finset.mem_insert.mp hOld with hxW | hxV
      · exact Or.inl (Or.inr hxW)
      · exact Or.inl (Or.inl
          ((forestFiniteMeetNodes_mem_iff V x).2 (Or.inl hxV)))
    · rcases Finset.mem_insert.mp ha with haW | haV
      · subst a
        rcases Finset.mem_insert.mp hb with hbW | hbV
        · subst b
          have hxW : x = w := hEq.symm.trans (forest_meet_self w)
          exact Or.inl (Or.inr hxW)
        · rcases Finset.mem_union.mp (hcross b hbV hRel) with hold | hy
          · have hOldX : x ∈ forestFiniteMeetNodes V := by
              rw [←hEq]
              exact hold
            exact Or.inl (Or.inl hOldX)
          · exact Or.inr (hEq.symm.trans (Finset.mem_singleton.mp hy))
      · rcases Finset.mem_insert.mp hb with hbW | hbV
        · subst b
          have hRel' : SMTree.Envelope.SameComponent w a := by
            obtain ⟨v,hva,hvw⟩ := hRel
            exact ⟨v,hvw,hva⟩
          have hEq' : LevelTree.meet w a = x :=
            (forest_meet_comm_of_related hRel').trans hEq
          rcases Finset.mem_union.mp (hcross a haV hRel') with hold | hy
          · have hOldX : x ∈ forestFiniteMeetNodes V := by
              rw [←hEq']
              exact hold
            exact Or.inl (Or.inl hOldX)
          · exact Or.inr (hEq'.symm.trans (Finset.mem_singleton.mp hy))
        · exact Or.inl (Or.inl
            ((forestFiniteMeetNodes_mem_iff V x).2
              (Or.inr ⟨a,haV,b,hbV,hRel,hEq⟩)))
  simpa only [Finset.mem_union, Finset.mem_singleton] using hMem

/-- The highest cross-meet is the only potential new branch point. -/
theorem forestFiniteMeetNodes_insert_cover (w : T) (V : Finset T) :
    ∃ y : T, forestFiniteMeetNodes (insert w V) ⊆
      (forestFiniteMeetNodes V ∪ {w}) ∪ {y} := by
  classical
  let W : Finset T := V.filter
    (fun a => SMTree.Envelope.SameComponent w a)
  by_cases hW : W.Nonempty
  · let C : Finset Nat := W.image
      (fun a => LevelTree.lev (LevelTree.meet w a))
    obtain ⟨a,ha⟩ := hW
    have hC : C.Nonempty :=
      ⟨LevelTree.lev (LevelTree.meet w a),
        Finset.mem_image.mpr ⟨a,ha,rfl⟩⟩
    obtain ⟨a0,ha0,hMax⟩ :=
      Finset.mem_image.mp (Finset.max'_mem C hC)
    obtain ⟨ha0V,ha0Related⟩ := Finset.mem_filter.mp ha0
    refine ⟨LevelTree.meet w a0,
      forestFiniteMeetNodes_insert_subset_of_cross w V
        (LevelTree.meet w a0) ?_⟩
    intro b hbV hwb
    have hbW : b ∈ W := Finset.mem_filter.mpr ⟨hbV,hwb⟩
    have hbC : LevelTree.lev (LevelTree.meet w b) ∈ C :=
      Finset.mem_image.mpr ⟨b,hbW,rfl⟩
    have hLevelBound :
        LevelTree.lev (LevelTree.meet w b) ≤
          LevelTree.lev (LevelTree.meet w a0) := by
      calc
        _ ≤ C.max' hC := Finset.le_max' C _ hbC
        _ = _ := hMax.symm
    have hMeetLe :
        LevelTree.meet w b ≤ LevelTree.meet w a0 := by
      rcases LevelTree.comparable_below
          (LevelTree.meet_le_left hwb)
          (LevelTree.meet_le_left ha0Related) with hle | hle
      · exact hle
      · have hLevels :
            LevelTree.lev (LevelTree.meet w a0) =
              LevelTree.lev (LevelTree.meet w b) := by
          have hReverse := LevelTree.level_le_of_le hle
          omega
        have hEq := LevelTree.same_level_of_le hle hLevels
        exact le_of_eq hEq.symm
    by_cases hEq : LevelTree.meet w b = LevelTree.meet w a0
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_singleton.mpr hEq))
    · have hStrict :
          LevelTree.meet w b < LevelTree.meet w a0 :=
        lt_of_le_of_ne hMeetLe hEq
      have hOldEq :
          LevelTree.meet w b = LevelTree.meet b a0 :=
        forest_strict_cross_meet_is_old hwb ha0Related hStrict
      have hOldRelated : SMTree.Envelope.SameComponent b a0 := by
        refine ⟨LevelTree.meet w b,LevelTree.meet_le_right hwb,?_⟩
        exact hStrict.le.trans (LevelTree.meet_le_right ha0Related)
      have hOld : LevelTree.meet w b ∈ forestFiniteMeetNodes V :=
        (forestFiniteMeetNodes_mem_iff V _).2
          (Or.inr ⟨b,hbV,a0,ha0V,hOldRelated,hOldEq⟩)
      exact Finset.mem_union.mpr (Or.inl hOld)
  · refine ⟨w,
      forestFiniteMeetNodes_insert_subset_of_cross w V w ?_⟩
    intro a ha hRelated
    have hMem : a ∈ W := Finset.mem_filter.mpr ⟨ha,hRelated⟩
    exact False.elim (hW ⟨a,hMem⟩)

/-- The manuscript's sharp finite forest meet-closure bound. -/
theorem forestFiniteMeetNodes_card_le_twice (V : Finset T) :
    (forestFiniteMeetNodes V).card ≤ 2 * V.card := by
  classical
  induction V using Finset.induction_on with
  | empty =>
      simp [forestFiniteMeetNodes]
  | @insert w V hw ih =>
      obtain ⟨y,hCover⟩ := forestFiniteMeetNodes_insert_cover w V
      have hBoundUnion :
          ((forestFiniteMeetNodes V ∪ {w}) ∪ {y}).card ≤
            (forestFiniteMeetNodes V).card + 2 := by
        have hA : (forestFiniteMeetNodes V ∪ {w}).card ≤
            (forestFiniteMeetNodes V).card + 1 := by
          simpa using Finset.card_union_le
            (forestFiniteMeetNodes V) ({w} : Finset T)
        have hB : ((forestFiniteMeetNodes V ∪ {w}) ∪ {y}).card ≤
            (forestFiniteMeetNodes V ∪ {w}).card + 1 := by
          simpa using Finset.card_union_le
            (forestFiniteMeetNodes V ∪ {w}) ({y} : Finset T)
        omega
      have hCardInsert : (insert w V).card = V.card + 1 :=
        Finset.card_insert_of_notMem hw
      calc
        (forestFiniteMeetNodes (insert w V)).card
            ≤ ((forestFiniteMeetNodes V ∪ {w}) ∪ {y}).card :=
          Finset.card_le_card hCover
        _ ≤ (forestFiniteMeetNodes V).card + 2 := hBoundUnion
        _ ≤ 2 * (insert w V).card := by omega

end SuccessorTree.V10