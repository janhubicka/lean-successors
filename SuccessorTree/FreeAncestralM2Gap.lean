import SuccessorTree.FreeAncestralM2Prep
import SuccessorTree.FreeAncestralCover
import Mathlib.Tactic

/-! # The outer one-gap factor for M2

Given a shape map F whose source level n lands on h+1 and skips h, the
lowered level-n images lie on level h and are pairwise distinct.  This file
chooses the one-gap map at h so that every lowered image is sent back to the
corresponding original F-image.

This is the outer factor F2 in M2; the inner factor F1 is assembled
separately.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat}
variable [Fintype Label] [Nonempty Label]

/-- The history component of a lowered top-level image, transported to the
literal index h. -/
noncomputable def lowerHistory
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    History Label arity h := by
  let z := lowerImage F n h hlevel x
  have hz : z.level = h :=
    lowerImage_level F n h hlevel x
  exact hz ▸ z.2

theorem lowerNode_eq_mk_lowerHistory
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    lowerImage F n h hlevel x =
      (⟨h, lowerHistory F n h hlevel x⟩ :
        Node Label arity) := by
  let z := lowerImage F n h hlevel x
  have hz : z.level = h :=
    lowerImage_level F n h hlevel x
  rcases z with ⟨k, zhist⟩
  change k = h at hz
  subst k
  rfl

theorem lowerHistory_injective
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1) :
    Function.Injective (lowerHistory F n h hlevel) := by
  intro x y hxy
  apply lowerImage_injective F n h hskip hlevel
  rw [lowerNode_eq_mk_lowerHistory,
      lowerNode_eq_mk_lowerHistory,
      hxy]

/-- Source level-n node whose lowered history is y, when one exists. -/
noncomputable def lowerSource?
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (y : History Label arity h) :
    Option {x : Node Label arity // x.level = n} := by
  classical
  exact if hex :
      ∃ x : {x : Node Label arity // x.level = n},
        lowerHistory F n h hlevel x = y then
    some (Classical.choose hex)
  else
    none

theorem lowerSource?_eq_some
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    lowerSource? F n h hlevel
        (lowerHistory F n h hlevel x) = some x := by
  classical
  unfold lowerSource?
  split
  next hex =>
    have hchosen :
        Classical.choose hex = x :=
      lowerHistory_injective F n h hskip hlevel
        (Classical.choose_spec hex)
    simp [hchosen]
  next hno =>
    exfalso
    apply hno
    exact ⟨x, rfl⟩

/-- The immediate cover from a lowered node to its original F-image. -/
noncomputable def lowerCover
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    (⟨h, lowerHistory F n h hlevel x⟩ :
        Node Label arity) ⋖ F x.1 := by
  rw [← lowerNode_eq_mk_lowerHistory]
  exact lowerImage_covBy F n h hlevel x

/-- Choice of the child inserted by the M2 outer one-gap map. -/
noncomputable def m2GapChoice
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (y : History Label arity h) :
    Code Label arity h := by
  classical
  match hs : lowerSource? F n h hlevel y with
  | some x =>
      have hy :
          y = lowerHistory F n h hlevel x := by
        unfold lowerSource? at hs
        split at hs
        next hex =>
          have hxopt :
              some (Classical.choose hex) = some x := hs
          have hx : Classical.choose hex = x :=
            Option.some.inj hxopt
          rw [← hx]
          exact (Classical.choose_spec hex).symm
        next hno =>
          simp at hs
      subst y
      exact coverCode (lowerCover F n h hlevel x)
  | none =>
      exact ⟨defaultLabel, emptyParamTuple arity h⟩

theorem m2GapChoice_lowerHistory
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    m2GapChoice F n h hlevel
        (lowerHistory F n h hlevel x) =
      coverCode (lowerCover F n h hlevel x) := by
  classical
  unfold m2GapChoice
  rw [lowerSource?_eq_some F n h hskip hlevel x]
  rfl

/-- The outer one-gap map sends every lowered top-level image back to its
original F-image. -/
theorem m2Gap_hits_lowerImage
    (F : ShapeMap (freeSTree (Label := Label) (arity := arity)))
    (n h : Nat)
    (hskip : F.Skips h)
    (hlevel :
      ∀ x : Node Label arity,
        x.level = n → (F x).level = h + 1)
    (x : {x : Node Label arity // x.level = n}) :
    oneGapShapeMap h (m2GapChoice F n h hlevel)
        (lowerImage F n h hlevel x) =
      F x.1 := by
  rw [lowerNode_eq_mk_lowerHistory F n h hlevel x]
  rw [oneGapShapeMap_apply, gapNode_at_level]
  rw [m2GapChoice_lowerHistory F n h hskip hlevel x]
  exact cover_eq_child (lowerCover F n h hlevel x)

end FreeAncestral
end SuccessorTree
