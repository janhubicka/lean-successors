import SuccessorTree.FreeAncestralGap
import Mathlib.Tactic

/-! # The raw one-gap map on free ancestral histories

For a fixed target gap level m, a choice function selects one immediate child
for every source node on level m.  The raw map is identity below m, takes the
chosen child at level m, and above m replays the old transition code with all
ancestral parameter levels shifted across the inserted gap.

The implementation deliberately returns a total history node together with its
target-level equation.  This avoids transporting indexed histories through the
piecewise level map at every recursive equation.
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

/-- Raw recursive one-gap map, packaged as a total node carrying its target
level equation. -/
noncomputable def gapNodeAux
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    (n : Nat) →
      History Label arity n →
      {x : Node Label arity // x.level = gapLevel m n}
  | 0, h => by
      have hroot : h = History.root := history_zero_unique h
      subst h
      by_cases hm : 0 < m
      · exact
          ⟨(⟨0, History.root⟩ : Node Label arity),
            (gapLevel_of_lt hm).symm⟩
      · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
        subst m
        exact
          ⟨(⟨1, History.step History.root (choose History.root)⟩ :
              Node Label arity),
            by simp [gapLevel]⟩
  | n + 1, h => by
      cases h with
      | step p c =>
          by_cases hlt : n + 1 < m
          · exact
              ⟨(⟨n + 1, History.step p c⟩ : Node Label arity),
                (gapLevel_of_lt hlt).symm⟩
          · by_cases heq : n + 1 = m
            · subst m
              exact
                ⟨(⟨n + 2,
                    History.step (History.step p c)
                      (choose (History.step p c))⟩ :
                    Node Label arity),
                  by simp [gapLevel]⟩
            · have hnge : m ≤ n := by omega
              let gp := gapNodeAux m choose n p
              let t' : ParamTuple arity gp.1.level :=
                { len := c.params.len
                  value := fun j =>
                    ⟨(shiftFin m n (c.params.value j)).val, by
                      rw [gp.2, gapLevel_of_ge hnge]
                      exact (shiftFin m n (c.params.value j)).isLt⟩ }
              let d : Node Label arity :=
                child gp.1 t' c.label
              refine ⟨d, ?_⟩
              dsimp [d]
              rw [child_level, gp.2,
                gapLevel_of_ge hnge,
                gapLevel_of_ge (by omega : m ≤ n + 1)]

/-- Total-node version of the raw one-gap recursion. -/
noncomputable def gapNode
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    Node Label arity :=
  (gapNodeAux m choose x.level x.2).1

@[simp] theorem gapNode_level
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (x : Node Label arity) :
    (gapNode m choose x).level = gapLevel m x.level :=
  (gapNodeAux m choose x.level x.2).2

theorem gapNode_level_of_lt
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level < m) :
    (gapNode m choose x).level = x.level := by
  rw [gapNode_level, gapLevel_of_lt hx]

theorem gapNode_level_of_ge
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : m ≤ x.level) :
    (gapNode m choose x).level = x.level + 1 := by
  rw [gapNode_level, gapLevel_of_ge hx]

theorem gapNode_eq_self_of_lt
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level < m) :
    gapNode m choose x = x := by
  rcases x with ⟨n, h⟩
  change n < m at hx
  cases n with
  | zero =>
      have hroot : h = History.root := history_zero_unique h
      subst h
      simp [gapNode, gapNodeAux, hx]
  | succ n =>
      cases h with
      | step p c =>
          simp [gapNode, gapNodeAux, hx]

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
      simp [gapNode, gapNodeAux, child, gapLevel]
  | succ n =>
      cases h with
      | step p c =>
          simp [gapNode, gapNodeAux, child, gapLevel]

/-- Shift a parameter tuple to the actual level of the gapped base node. -/
def gapShiftParamTuple
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : m ≤ a.level) :
    ParamTuple arity (gapNode m choose a).level where
  len := t.len
  value := fun j =>
    ⟨(shiftFin m a.level (t.value j)).val, by
      rw [gapNode_level_of_ge m choose ha]
      exact (shiftFin m a.level (t.value j)).isLt⟩

@[simp] theorem gapShiftParamTuple_len
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : m ≤ a.level) :
    (gapShiftParamTuple m choose a t ha).len = t.len := rfl

@[simp] theorem gapShiftParamTuple_value_val
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : m ≤ a.level)
    (j : Fin t.len.val) :
    ((gapShiftParamTuple m choose a t ha).value j).val =
      (shiftFin m a.level (t.value j)).val := rfl

theorem gapNode_child_of_ge
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label)
    (ha : m ≤ a.level) :
    gapNode m choose (child a t c) =
      child (gapNode m choose a)
        (gapShiftParamTuple m choose a t ha) c := by
  rcases a with ⟨n, h⟩
  change ParamTuple arity n at t
  change m ≤ n at ha
  change gapNode m choose
      (⟨n + 1, History.step h ⟨c, t⟩⟩ :
        Node Label arity) =
    child (gapNode m choose (⟨n, h⟩ : Node Label arity))
      (gapShiftParamTuple m choose
        (⟨n, h⟩ : Node Label arity) t ha) c
  unfold gapNode
  simp only [gapNodeAux]
  rw [dif_neg (by omega : ¬ n + 1 < m)]
  rw [dif_neg (by omega : ¬ n + 1 = m)]
  let gp := gapNodeAux m choose n h
  change
    child gp.1
        { len := t.len
          value := fun j =>
            ⟨(shiftFin m n (t.value j)).val, by
              rw [gp.2, gapLevel_of_ge ha]
              exact (shiftFin m n (t.value j)).isLt⟩ } c =
      child (gapNodeAux m choose n h).1
        (gapShiftParamTuple m choose
          (⟨n, h⟩ : Node Label arity) t ha) c
  congr 1
  apply ParamTuple.ext
  · rfl
  · funext j
    apply Fin.ext
    rfl

theorem gapLevel_injective (m : Nat) :
    Function.Injective (gapLevel m) := by
  intro i j hij
  unfold gapLevel at hij
  by_cases hi : i < m <;> by_cases hj : j < m <;>
    simp [hi, hj] at hij ⊢ <;> omega

theorem levelList_gapShiftParamTuple
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : m ≤ a.level) :
    levelList (gapShiftParamTuple m choose a t ha) =
      (levelList t).map (shiftNat m) := by
  simp only [levelList, gapShiftParamTuple, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  by_cases hj : (t.value j).val < m
  · simp [shiftNat, shiftFin, hj, Function.comp_def]
  · simp [shiftNat, shiftFin, hj, Function.comp_def]

theorem gapShiftParamTuple_injective
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (ha : m ≤ a.level) :
    Function.Injective
      (fun t : ParamTuple arity a.level =>
        gapShiftParamTuple m choose a t ha) := by
  intro t u htu
  apply levelList_injective
  have hlevels :=
    congrArg (levelList (arity := arity)) htu
  rw [levelList_gapShiftParamTuple,
      levelList_gapShiftParamTuple] at hlevels
  exact
    list_map_injective_of_injective
      (shiftNat_injective m) hlevels

theorem gapNode_injective_at_level
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    ∀ n : Nat,
      Function.Injective
        (fun h : History Label arity n =>
          gapNode m choose (⟨n, h⟩ : Node Label arity))
  | 0 => by
      intro x y hxy
      exact (history_zero_unique x).trans
        (history_zero_unique y).symm
  | n + 1 => by
      intro x y hxy
      by_cases hlt : n + 1 < m
      · have hxid :
            gapNode m choose
                (⟨n + 1, x⟩ : Node Label arity) =
              (⟨n + 1, x⟩ : Node Label arity) :=
          gapNode_eq_self_of_lt m choose hlt
        have hyid :
            gapNode m choose
                (⟨n + 1, y⟩ : Node Label arity) =
              (⟨n + 1, y⟩ : Node Label arity) :=
          gapNode_eq_self_of_lt m choose hlt
        have hnode :
            (⟨n + 1, x⟩ : Node Label arity) =
              (⟨n + 1, y⟩ : Node Label arity) := by
          rw [← hxid, ← hyid]
          exact hxy
        exact eq_of_heq (Sigma.mk.inj_iff.mp hnode).2
      · by_cases heq : n + 1 = m
        · subst m
          change
            gapNode (n + 1) choose
                (⟨n + 1, x⟩ : Node Label arity) =
              gapNode (n + 1) choose
                (⟨n + 1, y⟩ : Node Label arity)
            at hxy
          rw [gapNode_at_level, gapNode_at_level] at hxy
          have hbase :=
            base_eq_of_child_eq hxy
          exact eq_of_heq (Sigma.mk.inj_iff.mp hbase).2
        · have hnge : m ≤ n := by omega
          cases x with
          | step px cx =>
              cases y with
              | step py cy =>
                  have hxform :=
                    gapNode_child_of_ge m choose
                      (⟨n, px⟩ : Node Label arity)
                      cx.params cx.label hnge
                  have hyform :=
                    gapNode_child_of_ge m choose
                      (⟨n, py⟩ : Node Label arity)
                      cy.params cy.label hnge
                  rw [hxform, hyform] at hxy
                  have hbase :
                      gapNode m choose
                          (⟨n, px⟩ : Node Label arity) =
                        gapNode m choose
                          (⟨n, py⟩ : Node Label arity) :=
                    base_eq_of_child_eq hxy
                  have hp :
                      px = py :=
                    gapNode_injective_at_level m choose n hbase
                  subst py
                  have hdata := child_eq_data hxy
                  have hparams :
                      cx.params = cy.params :=
                    gapShiftParamTuple_injective
                      m choose (⟨n, px⟩ : Node Label arity)
                      hnge hdata.1
                  have hlabel : cx.label = cy.label := hdata.2
                  cases cx with
                  | mk cl cp =>
                      cases cy with
                      | mk dl dp =>
                          simp only at hparams hlabel
                          subst dl
                          subst dp
                          rfl

theorem gapNode_injective
    (m : Nat)
    (choose : History Label arity m → Code Label arity m) :
    Function.Injective (gapNode m choose) := by
  intro x y hxy
  have hlevels :
      gapLevel m x.level = gapLevel m y.level := by
    rw [← gapNode_level m choose x,
        ← gapNode_level m choose y, hxy]
  have hsrc : x.level = y.level :=
    gapLevel_injective m hlevels
  rcases x with ⟨nx, hx⟩
  rcases y with ⟨ny, hy⟩
  change nx = ny at hsrc
  subst ny
  have hhist :
      gapNode m choose (⟨nx, hx⟩ : Node Label arity) =
        gapNode m choose (⟨nx, hy⟩ : Node Label arity) :=
    hxy
  have heq :
      hx = hy :=
    gapNode_injective_at_level m choose nx hhist
  subst hy
  rfl


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
      change
        (⟨n, h⟩ : Node Label arity) ≤
          gapNode (n + 1) choose
            (⟨n + 1, History.step h ⟨c, t⟩⟩ :
              Node Label arity)
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
  rcases x with ⟨lx, hx⟩
  rcases y with ⟨ly, hy⟩
  change Prefix hx hy at hxy
  induction hxy with
  | refl => exact le_rfl
  | step hp code ih =>
      apply le_trans ih
      apply gapNode_base_le_child

theorem paramNodes_lift_of_le
    {a b : Node Label arity}
    (hab : a ≤ b)
    (t : ParamTuple arity a.level) :
    paramNodes b
        (liftParamTuple (node_level_le hab) t) =
      paramNodes a t := by
  simp only [paramNodes]
  apply congrArg List.ofFn
  funext j
  have hk :
      (t.value j).val ≤ a.level :=
    Nat.le_of_lt (t.value j).isLt
  have hxa :
      LevelTree.ancestor a (t.value j).val hk ≤ b :=
    (LevelTree.ancestor_le a (t.value j).val hk).trans hab
  have hlev :
      LevelTree.lev
          (LevelTree.ancestor a (t.value j).val hk) =
        (t.value j).val :=
    LevelTree.level_ancestor a (t.value j).val hk
  have htarget :
      (t.value j).val ≤ b.level :=
    (Nat.le_of_lt (t.value j).isLt).trans
      (node_level_le hab)
  have heq :=
    LevelTree.eq_ancestor_of_le hxa hlev htarget
  simpa [liftParamTuple, liftFin] using heq.symm

theorem le_gapNode_of_level_eq
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level = m) :
    x ≤ gapNode m choose x := by
  rcases x with ⟨n, h⟩
  change n = m at hx
  subst n
  rw [gapNode_at_level]
  exact base_le_child _ _ _

theorem map_paramNodes_gap_of_lt
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : a.level < m) :
    (paramNodes a t).map (gapNode m choose) =
      paramNodes a t := by
  simp only [paramNodes, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  apply gapNode_eq_self_of_lt
  change LevelTree.lev
      (LevelTree.ancestor a (t.value j).val
        (Nat.le_of_lt (t.value j).isLt)) < m
  rw [LevelTree.level_ancestor]
  exact (t.value j).isLt.trans ha

theorem map_paramNodes_gap_of_ge
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : m ≤ a.level) :
    (paramNodes a t).map (gapNode m choose) =
      paramNodes (gapNode m choose a)
        (gapShiftParamTuple m choose a t ha) := by
  simp only [paramNodes, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  let x :=
    LevelTree.ancestor a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)
  have hxa : x ≤ a :=
    LevelTree.ancestor_le a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)
  have hmaple :
      gapNode m choose x ≤ gapNode m choose a :=
    gapNode_monotone m choose hxa
  have htarget :
      ((gapShiftParamTuple m choose a t ha).value j).val <
        (gapNode m choose a).level := by
    exact ((gapShiftParamTuple m choose a t ha).value j).isLt
  have hxlev :
      (gapNode m choose x).level =
        ((gapShiftParamTuple m choose a t ha).value j).val := by
    dsimp [x]
    change
      gapLevel m
          (LevelTree.lev
            (LevelTree.ancestor a (t.value j).val
              (Nat.le_of_lt (t.value j).isLt))) =
        (shiftFin m a.level (t.value j)).val
    rw [LevelTree.level_ancestor]
    by_cases hj : (t.value j).val < m
    · simp [gapLevel, shiftFin, hj]
    · simp [gapLevel, shiftFin, hj]
  exact LevelTree.eq_ancestor_of_le
    hmaple hxlev (Nat.le_of_lt htarget)

theorem gapNode_weak_succ
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {a b : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (h : freeSucc a p c = some b) :
    ∃ d : Node Label arity,
      freeSucc (gapNode m choose a)
          (p.map (gapNode m choose)) c = some d ∧
        d ≤ gapNode m choose b := by
  obtain ⟨t, htp, hbeq⟩ :=
    freeSucc_eq_some_data h
  subst b
  subst p
  by_cases ha : a.level < m
  · have hDa :
        gapNode m choose a = a :=
      gapNode_eq_self_of_lt m choose ha
    have hparams :
        (paramNodes a t).map (gapNode m choose) =
          paramNodes a t :=
      map_paramNodes_gap_of_lt m choose a t ha
    refine ⟨child a t c, ?_, ?_⟩
    · rw [hDa, hparams]
      exact freeSucc_paramNodes a t c
    · by_cases hb :
          (child a t c).level < m
      · rw [gapNode_eq_self_of_lt m choose hb]
      · have hb' : ¬ a.level + 1 < m := by
          simpa [child_level] using hb
        have hblevel :
            (child a t c).level = m := by
          rw [child_level]
          omega
        exact le_gapNode_of_level_eq m choose hblevel
  · have hge : m ≤ a.level :=
      Nat.le_of_not_gt ha
    refine
      ⟨gapNode m choose (child a t c), ?_, le_rfl⟩
    rw [map_paramNodes_gap_of_ge m choose a t hge]
    rw [gapNode_child_of_ge m choose a t c hge]
    exact freeSucc_paramNodes
      (gapNode m choose a)
      (gapShiftParamTuple m choose a t hge) c

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
    x = (rootNode (Label := Label) (arity := arity)) := by
  have hroot :
      (rootNode (Label := Label) (arity := arity)) ≤ x :=
    root_le x
  have hlev :
      (rootNode (Label := Label) (arity := arity)).level =
        x.level := by
    simpa [rootNode, Node.level] using hx.symm
  exact (node_eq_of_le_level_eq hroot hlev).symm

theorem root_le_gapNode
    (m : Nat)
    (choose : History Label arity m → Code Label arity m)
    {x : Node Label arity}
    (hx : x.level = 0) :
    x ≤ gapNode m choose x := by
  have hxroot :
      x = (rootNode (Label := Label) (arity := arity)) :=
    level_zero_eq_root hx
  subst x
  exact root_le
    (gapNode m choose
      (rootNode (Label := Label) (arity := arity)))

end FreeAncestral
end SuccessorTree
