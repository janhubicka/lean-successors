import SuccessorTree.FreeAncestralM2Inner
import Mathlib.Tactic

/-! # Order and parameter transport for the inner M2 map -/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

theorem m2InnerNode_base_le_child
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    m2InnerNode F n h hskip hlevel a ≤
      m2InnerNode F n h hskip hlevel (child a t c) := by
  by_cases ha : a.level < n
  · have hsuccLe : a.level + 1 ≤ n := by omega
    by_cases hchild : (child a t c).level < n
    · rw [m2InnerNode_eq_F_of_lt F n h hskip hlevel ha]
      rw [m2InnerNode_eq_F_of_lt F n h hskip hlevel hchild]
      exact F.map_le_of_le (base_le_child a t c)
    · have hcut : (child a t c).level = n := by
        rw [child_level] at hchild ⊢
        omega
      let xb : {x : Node Label arity // x.level = n} :=
        ⟨child a t c, hcut⟩
      rw [m2InnerNode_eq_F_of_lt F n h hskip hlevel ha]
      rw [m2InnerNode_at_cut F n h hskip hlevel xb]
      have hFaChild :
          F a ≤ F (child a t c) :=
        F.map_le_of_le (base_le_child a t c)
      have hzChild :
          lowerImage F n h hlevel xb ≤
            F (child a t c) :=
        lowerImage_le F n h hlevel xb
      rcases LevelTree.comparable_below hFaChild hzChild with hFz | hzF
      · exact hFz
      · have hFaLev :
            (F a).level = imageLevel F a.level :=
          imageLevel_eq F rfl
        have hFaLt :
            (F a).level < h := by
          rw [hFaLev]
          exact imageLevel_below_lt_missing
            F n h a.level ha hskip hlevel
        have hzLev :
            (lowerImage F n h hlevel xb).level = h :=
          lowerImage_level F n h hlevel xb
        have hlevels := node_level_le hzF
        rw [hzLev] at hlevels
        omega
  · have hge : n ≤ a.level := Nat.le_of_not_gt ha
    rw [m2InnerNode_child_of_ge F n h hskip hlevel a t c hge]
    exact base_le_child _ _ _

theorem m2InnerNode_monotone
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    {x y : Node Label arity}
    (hxy : x ≤ y) :
    m2InnerNode F n h hskip hlevel x ≤
      m2InnerNode F n h hskip hlevel y := by
  rcases x with ⟨lx, hx⟩
  rcases y with ⟨ly, hy⟩
  change Prefix hx hy at hxy
  induction hxy with
  | refl => exact le_rfl
  | step hp code ih =>
      exact ih.trans
        (m2InnerNode_base_le_child
          F n h hskip hlevel
          (⟨_, _⟩ : Node Label arity)
          code.params code.label)

theorem map_paramNodes_m2Inner
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    (paramNodes a t).map
        (m2InnerNode F n h hskip hlevel) =
      paramNodes
        (m2InnerNode F n h hskip hlevel a)
        (m2InnerParamTupleAt
          F n h hskip hlevel a t) := by
  simp only [paramNodes, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  let x :=
    LevelTree.ancestor a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)
  have hxa : x ≤ a :=
    LevelTree.ancestor_le a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)
  have hmap :
      m2InnerNode F n h hskip hlevel x ≤
        m2InnerNode F n h hskip hlevel a :=
    m2InnerNode_monotone F n h hskip hlevel hxa
  have hxlev : x.level = (t.value j).val := by
    dsimp [x]
    exact LevelTree.level_ancestor
      a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)
  have hmaplev :
      (m2InnerNode F n h hskip hlevel x).level =
        ((m2InnerParamTupleAt
          F n h hskip hlevel a t).value j).val := by
    rw [m2InnerNode_level, hxlev]
    rfl
  have htarget :
      ((m2InnerParamTupleAt
        F n h hskip hlevel a t).value j).val <
        (m2InnerNode F n h hskip hlevel a).level :=
    ((m2InnerParamTupleAt
      F n h hskip hlevel a t).value j).isLt
  exact LevelTree.eq_ancestor_of_le
    hmap hmaplev (Nat.le_of_lt htarget)


theorem levelList_m2InnerParamTupleAt
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    levelList (m2InnerParamTupleAt F n h hskip hlevel a t) =
      (levelList t).map (m2InnerLevel F n h) := by
  simp only [levelList, m2InnerParamTupleAt, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  rfl

theorem m2InnerParamTupleAt_injective
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity) :
    Function.Injective
      (m2InnerParamTupleAt F n h hskip hlevel a) := by
  intro t u htu
  apply levelList_injective
  have hlevels :=
    congrArg (levelList (arity := arity)) htu
  rw [levelList_m2InnerParamTupleAt,
      levelList_m2InnerParamTupleAt] at hlevels
  exact
    list_map_injective_of_injective
      (m2InnerLevel_strictMono F n h hskip hlevel).injective
      hlevels


end FreeAncestral
end SuccessorTree
