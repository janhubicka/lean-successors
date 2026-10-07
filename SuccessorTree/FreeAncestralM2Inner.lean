import SuccessorTree.FreeAncestralM2Level
import Mathlib.Tactic

/-! # Raw inner map for M2 on the free ancestral tree

Below the source cut n the map follows F. At source level n it lowers the
image by one level to the missing target level h. Above n it replays the
source transition codes consecutively, transporting ancestral parameter
levels through m2InnerLevel.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

noncomputable def m2InnerNodeAux
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    (k : Nat) →
      History Label arity k →
      {x : Node Label arity //
        x.level = m2InnerLevel F n h k}
  | 0, hist => by
      by_cases hn : 0 < n
      · let x : Node Label arity := ⟨0, hist⟩
        refine ⟨F x, ?_⟩
        rw [m2InnerLevel_of_lt F hn]
        exact imageLevel_eq F rfl
      · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        let x : {x : Node Label arity // x.level = 0} :=
          ⟨⟨0, hist⟩, rfl⟩
        refine ⟨lowerImage F 0 h hlevel x, ?_⟩
        simpa using lowerImage_level F 0 h hlevel x
  | k + 1, hist => by
      by_cases hlt : k + 1 < n
      · let x : Node Label arity := ⟨k + 1, hist⟩
        refine ⟨F x, ?_⟩
        rw [m2InnerLevel_of_lt F hlt]
        exact imageLevel_eq F rfl
      · by_cases heq : k + 1 = n
        · subst n
          let x : {x : Node Label arity // x.level = k + 1} :=
            ⟨⟨k + 1, hist⟩, rfl⟩
          refine ⟨lowerImage F (k + 1) h hlevel x, ?_⟩
          simpa using lowerImage_level F (k + 1) h hlevel x
        · have hge : n ≤ k := by omega
          cases hist with
          | step p c =>
              let gp :=
                m2InnerNodeAux F n h hskip hlevel k p
              let t' : ParamTuple arity gp.1.level :=
                { len := c.params.len
                  value := fun j =>
                    ⟨m2InnerLevel F n h (c.params.value j).val, by
                      rw [gp.2]
                      exact m2InnerLevel_strictMono F n h hskip hlevel
                        (c.params.value j).isLt⟩ }
              let d : Node Label arity :=
                child gp.1 t' c.label
              refine ⟨d, ?_⟩
              dsimp [d]
              rw [child_level, gp.2,
                m2InnerLevel_of_ge F hge,
                m2InnerLevel_of_ge F (by omega : n ≤ k + 1)]
              omega

noncomputable def m2InnerNode
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : Node Label arity) :
    Node Label arity :=
  (m2InnerNodeAux F n h hskip hlevel x.level x.2).1

@[simp] theorem m2InnerNode_level
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : Node Label arity) :
    (m2InnerNode F n h hskip hlevel x).level =
      m2InnerLevel F n h x.level :=
  (m2InnerNodeAux F n h hskip hlevel x.level x.2).2


/-- Transport the numerical M2 parameter tuple to the literal level index of
the recursive image node. -/
noncomputable def m2InnerParamTupleAt
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    ParamTuple arity (m2InnerNode F n h hskip hlevel a).level where
  len := t.len
  value := fun j =>
    ⟨m2InnerLevel F n h (t.value j).val, by
      rw [m2InnerNode_level]
      exact m2InnerLevel_strictMono F n h hskip hlevel
        (t.value j).isLt⟩

@[simp] theorem m2InnerParamTupleAt_len
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    (m2InnerParamTupleAt F n h hskip hlevel a t).len = t.len := rfl

@[simp] theorem m2InnerParamTupleAt_value_val
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (j : Fin t.len.val) :
    ((m2InnerParamTupleAt F n h hskip hlevel a t).value j).val =
      m2InnerLevel F n h (t.value j).val := rfl

theorem m2InnerNode_eq_F_of_lt
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    {x : Node Label arity}
    (hx : x.level < n) :
    m2InnerNode F n h hskip hlevel x = F x := by
  rcases x with ⟨k, hist⟩
  change k < n at hx
  cases k with
  | zero =>
      change
        (m2InnerNodeAux F n h hskip hlevel 0 hist).1 =
          F (⟨0, hist⟩ : Node Label arity)
      simp [m2InnerNodeAux, hx]
  | succ k =>
      change
        (m2InnerNodeAux F n h hskip hlevel (k + 1) hist).1 =
          F (⟨k + 1, hist⟩ : Node Label arity)
      simp [m2InnerNodeAux, hx]

theorem m2InnerNode_at_cut
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    m2InnerNode F n h hskip hlevel x.1 =
      lowerImage F n h hlevel x := by
  rcases x with ⟨⟨k, hist⟩, hk⟩
  change k = n at hk
  subst k
  cases n with
  | zero =>
      change
        (m2InnerNodeAux F 0 h hskip hlevel 0 hist).1 =
          lowerImage F 0 h hlevel
            ⟨⟨0, hist⟩, rfl⟩
      simp [m2InnerNodeAux]
  | succ k =>
      change
        (m2InnerNodeAux F (k + 1) h hskip hlevel
          (k + 1) hist).1 =
          lowerImage F (k + 1) h hlevel
            ⟨⟨k + 1, hist⟩, rfl⟩
      simp [m2InnerNodeAux]

theorem m2InnerNode_child_of_ge
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label)
    (ha : n ≤ a.level) :
    m2InnerNode F n h hskip hlevel (child a t c) =
      child (m2InnerNode F n h hskip hlevel a)
        (m2InnerParamTupleAt
          F n h hskip hlevel a t) c := by
  rcases a with ⟨k, hist⟩
  change n ≤ k at ha
  change
    (m2InnerNodeAux F n h hskip hlevel (k + 1)
      (History.step hist ⟨c, t⟩)).1 =
      child
        (m2InnerNodeAux F n h hskip hlevel k hist).1
        (m2InnerParamTupleAt
          F n h hskip hlevel
          (⟨k, hist⟩ : Node Label arity) t) c
  rw [m2InnerNodeAux]
  rw [dif_neg (by omega : ¬ k + 1 < n)]
  rw [dif_neg (by omega : ¬ k + 1 = n)]
  let gp :=
    m2InnerNodeAux F n h hskip hlevel k hist
  change
    child gp.1
        { len := t.len
          value := fun j =>
            ⟨m2InnerLevel F n h (t.value j).val, by
              rw [gp.2]
              exact m2InnerLevel_strictMono F n h hskip hlevel
                (t.value j).isLt⟩ } c =
      child gp.1
        (m2InnerParamTupleAt F n h hskip hlevel
          (⟨k, hist⟩ : Node Label arity) t) c
  congr 1
  apply (paramTupleEquiv arity _).injective
  apply Sigma.ext rfl
  apply HEq.of_eq
  funext j
  apply Fin.ext
  rfl

end FreeAncestral
end SuccessorTree
