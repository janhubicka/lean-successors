import SuccessorTree.FreeAncestralM2InnerOrder
import Mathlib.Tactic

/-! # Shape-map structure of the inner M2 factor -/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

theorem m2InnerNode_injective_at_level
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    ∀ k : Nat,
      Function.Injective
        (fun hist : History Label arity k =>
          m2InnerNode F n h hskip hlevel
            (⟨k, hist⟩ : Node Label arity))
  | 0 => by
      intro x y hxy
      by_cases hn : 0 < n
      · have hxy' :
            F (⟨0, x⟩ : Node Label arity) =
              F (⟨0, y⟩ : Node Label arity) := by
          simpa [m2InnerNode_eq_F_of_lt F n h hskip hlevel hn]
            using hxy
        have hnode := F.injective hxy'
        exact eq_of_heq (Sigma.mk.inj_iff.mp hnode).2
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        let sx : {z : Node Label arity // z.level = 0} :=
          ⟨⟨0, x⟩, rfl⟩
        let sy : {z : Node Label arity // z.level = 0} :=
          ⟨⟨0, y⟩, rfl⟩
        have hlow :
            lowerImage F 0 h hlevel sx =
              lowerImage F 0 h hlevel sy := by
          simpa [sx, sy,
            m2InnerNode_at_cut F 0 h hskip hlevel] using hxy
        have hsxy :
            sx = sy :=
          lowerImage_injective F 0 h hskip hlevel hlow
        exact eq_of_heq (Sigma.mk.inj_iff.mp
          (congrArg Subtype.val hsxy)).2
  | k + 1 => by
      intro x y hxy
      by_cases hlt : k + 1 < n
      · have hxy' :
            F (⟨k + 1, x⟩ : Node Label arity) =
              F (⟨k + 1, y⟩ : Node Label arity) := by
          simpa [m2InnerNode_eq_F_of_lt F n h hskip hlevel hlt]
            using hxy
        have hnode := F.injective hxy'
        exact eq_of_heq (Sigma.mk.inj_iff.mp hnode).2
      · by_cases heq : k + 1 = n
        · let sx : {z : Node Label arity // z.level = n} :=
            ⟨⟨k + 1, x⟩, heq⟩
          let sy : {z : Node Label arity // z.level = n} :=
            ⟨⟨k + 1, y⟩, heq⟩
          have hlow :
              lowerImage F n h hlevel sx =
                lowerImage F n h hlevel sy := by
            simpa [sx, sy,
              m2InnerNode_at_cut F n h hskip hlevel] using hxy
          have hsxy :
              sx = sy :=
            lowerImage_injective F n h hskip hlevel hlow
          exact eq_of_heq (Sigma.mk.inj_iff.mp
            (congrArg Subtype.val hsxy)).2
        · have hge : n ≤ k := by omega
          cases x with
          | step px cx =>
              cases y with
              | step py cy =>
                  change
                    m2InnerNode F n h hskip hlevel
                        (child (⟨k, px⟩ : Node Label arity)
                          cx.params cx.label) =
                      m2InnerNode F n h hskip hlevel
                        (child (⟨k, py⟩ : Node Label arity)
                          cy.params cy.label)
                    at hxy
                  rw [m2InnerNode_child_of_ge
                        F n h hskip hlevel
                        (⟨k, px⟩ : Node Label arity)
                        cx.params cx.label hge,
                      m2InnerNode_child_of_ge
                        F n h hskip hlevel
                        (⟨k, py⟩ : Node Label arity)
                        cy.params cy.label hge] at hxy
                  have hbase :
                      m2InnerNode F n h hskip hlevel
                          (⟨k, px⟩ : Node Label arity) =
                        m2InnerNode F n h hskip hlevel
                          (⟨k, py⟩ : Node Label arity) :=
                    base_eq_of_child_eq hxy
                  have hp :
                      px = py :=
                    m2InnerNode_injective_at_level
                      F n h hskip hlevel k hbase
                  subst py
                  have hdata := child_eq_data hxy
                  have hparams :
                      cx.params = cy.params :=
                    m2InnerParamTuple_injective
                      F n h hskip hlevel k hdata.1
                  have hlabel : cx.label = cy.label := hdata.2
                  cases cx with
                  | mk cl cp =>
                      cases cy with
                      | mk dl dp =>
                          simp only at hparams hlabel
                          subst dl
                          subst dp
                          rfl

theorem m2InnerNode_injective
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    Function.Injective (m2InnerNode F n h hskip hlevel) := by
  intro x y hxy
  have hlev :
      m2InnerLevel F n h x.level =
        m2InnerLevel F n h y.level := by
    rw [← m2InnerNode_level F n h hskip hlevel x,
        ← m2InnerNode_level F n h hskip hlevel y,
        hxy]
  have hsrc :
      x.level = y.level :=
    (m2InnerLevel_strictMono F n h hskip hlevel).injective hlev
  rcases x with ⟨kx, hx⟩
  rcases y with ⟨ky, hy⟩
  change kx = ky at hsrc
  subst ky
  have hhist :
      m2InnerNode F n h hskip hlevel
          (⟨kx, hx⟩ : Node Label arity) =
        m2InnerNode F n h hskip hlevel
          (⟨kx, hy⟩ : Node Label arity) :=
    hxy
  have hxyHist :
      hx = hy :=
    m2InnerNode_injective_at_level
      F n h hskip hlevel kx hhist
  subst hy
  rfl

theorem map_paramNodes_m2Inner_eq_F_of_lt
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (ha : a.level < n) :
    (paramNodes a t).map
        (m2InnerNode F n h hskip hlevel) =
      (paramNodes a t).map F := by
  simp only [paramNodes, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  apply m2InnerNode_eq_F_of_lt
  change
    LevelTree.lev
      (LevelTree.ancestor a (t.value j).val
        (Nat.le_of_lt (t.value j).isLt)) < n
  rw [LevelTree.level_ancestor]
  exact (t.value j).isLt.trans ha

theorem m2InnerNode_weak_succ
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    {a b : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (hsucc : freeSucc a p c = some b) :
    ∃ d : Node Label arity,
      freeSucc
        (m2InnerNode F n h hskip hlevel a)
        (p.map (m2InnerNode F n h hskip hlevel)) c =
          some d ∧
        d ≤ m2InnerNode F n h hskip hlevel b := by
  obtain ⟨t, htp, hbeq⟩ :=
    freeSucc_eq_some_data hsucc
  subst b
  subst p
  by_cases ha : a.level < n
  · have hsucLe : a.level + 1 ≤ n := by omega
    by_cases hb :
        (child a t c).level < n
    · obtain ⟨d, hFd, hdb⟩ :=
        F.weak_succ'
          (freeSucc_paramNodes a t c)
      have hbase :
          m2InnerNode F n h hskip hlevel a = F a :=
        m2InnerNode_eq_F_of_lt F n h hskip hlevel ha
      have hchild :
          m2InnerNode F n h hskip hlevel (child a t c) =
            F (child a t c) :=
        m2InnerNode_eq_F_of_lt F n h hskip hlevel hb
      have hparams :
          (paramNodes a t).map
              (m2InnerNode F n h hskip hlevel) =
            (paramNodes a t).map F :=
        map_paramNodes_m2Inner_eq_F_of_lt
          F n h hskip hlevel a t ha
      refine ⟨d, ?_, ?_⟩
      · simpa [hbase, hparams] using hFd
      · simpa [hchild] using hdb
    · have hcut :
          (child a t c).level = n := by
        rw [child_level] at hb ⊢
        omega
      let xb : {x : Node Label arity // x.level = n} :=
        ⟨child a t c, hcut⟩
      obtain ⟨d, hFd, hdb⟩ :=
        F.weak_succ'
          (freeSucc_paramNodes a t c)
      have hbase :
          m2InnerNode F n h hskip hlevel a = F a :=
        m2InnerNode_eq_F_of_lt F n h hskip hlevel ha
      have hparams :
          (paramNodes a t).map
              (m2InnerNode F n h hskip hlevel) =
            (paramNodes a t).map F :=
        map_paramNodes_m2Inner_eq_F_of_lt
          F n h hskip hlevel a t ha
      have hinnerChild :
          m2InnerNode F n h hskip hlevel (child a t c) =
            lowerImage F n h hlevel xb := by
        exact m2InnerNode_at_cut F n h hskip hlevel xb
      have hzChild :
          lowerImage F n h hlevel xb ≤
            F (child a t c) :=
        lowerImage_le F n h hlevel xb
      have hdCover :
          F a ⋖ d :=
        freeSTree.covBy_of_succ_eq_some hFd
      have hFaLev :
          (F a).level = imageLevel F a.level :=
        imageLevel_eq F rfl
      have hFaLt :
          (F a).level < h := by
        rw [hFaLev]
        exact imageLevel_below_lt_missing
          F n h a.level ha hskip hlevel
      have hdLev :
          d.level = (F a).level + 1 :=
        LevelTree.covBy_level_eq hdCover
      have hzLev :
          (lowerImage F n h hlevel xb).level = h :=
        lowerImage_level F n h hlevel xb
      have hdLeZ :
          d ≤ lowerImage F n h hlevel xb := by
        rcases LevelTree.comparable_below hdb hzChild with hdz | hzd
        · exact hdz
        · have hlevle := node_level_le hzd
          rw [hdLev, hzLev] at hlevle
          have heqLev :
              (lowerImage F n h hlevel xb).level = d.level := by
            rw [hzLev, hdLev]
            omega
          have heq :
              lowerImage F n h hlevel xb = d :=
            node_eq_of_le_level_eq hzd heqLev
          simpa [heq]
      refine ⟨d, ?_, ?_⟩
      · simpa [hbase, hparams] using hFd
      · simpa [hinnerChild] using hdLeZ
  · have hge : n ≤ a.level := Nat.le_of_not_gt ha
    let t' :=
      m2InnerParamTuple
        F n h hskip hlevel a.level t
    let d :=
      child (m2InnerNode F n h hskip hlevel a) t' c
    refine ⟨d, ?_, ?_⟩
    · rw [map_paramNodes_m2Inner
            F n h hskip hlevel a t]
      exact freeSucc_paramNodes
        (m2InnerNode F n h hskip hlevel a) t' c
    · dsimp [d, t']
      rw [← m2InnerNode_child_of_ge
            F n h hskip hlevel a t c hge]
      exact le_rfl

noncomputable def m2InnerShapeMap
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    ShapeMap (freeSTree (Label := Label) (arity := arity)) where
  toFun := m2InnerNode F n h hskip hlevel
  injective' := m2InnerNode_injective F n h hskip hlevel
  level_preserving' := by
    intro a b hab
    rw [m2InnerNode_level, m2InnerNode_level, hab]
  weak_succ' := by
    intro a b p c hsucc
    exact m2InnerNode_weak_succ F n h hskip hlevel hsucc
  root_le' := by
    intro a ha
    exact root_le (m2InnerNode F n h hskip hlevel a)

@[simp] theorem m2InnerShapeMap_apply
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : Node Label arity) :
    m2InnerShapeMap F n h hskip hlevel x =
      m2InnerNode F n h hskip hlevel x := rfl

end FreeAncestral
end SuccessorTree
