import SuccessorTree.Support
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-!
# Equivariance of starred Hales--Jewett

Renaming the alphabet by an equivalence preserves starred lines and
monochromaticity.
-/

namespace SuccessorTree
namespace HalesJewett

def mapLineSymbol (f : α → β) : LineSymbol α → LineSymbol β
  | .const a => .const (f a)
  | .parameter => .parameter

def mapLineWord (f : α → β) (w : List (LineSymbol α)) :
    List (LineSymbol β) :=
  w.map (mapLineSymbol f)

theorem starPrefix_mapLineWord
    (f : α → β) (w : List (LineSymbol α)) :
    starPrefix (mapLineWord f w) = (starPrefix w).map f := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | parameter => rfl
      | const a =>
          change f a :: starPrefix (mapLineWord f xs) =
            f a :: (starPrefix xs).map f
          exact congrArg (List.cons (f a)) ih

theorem evalWord_mapLineWord
    (f : α → β) (a : α) (w : List (LineSymbol α)) :
    evalWord (f a) (mapLineWord f w) =
      (evalWord a w).map f := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | parameter =>
          change f a :: evalWord (f a) (mapLineWord f xs) =
            f a :: (evalWord a xs).map f
          exact congrArg (List.cons (f a)) ih
      | const b =>
          change f b :: evalWord (f a) (mapLineWord f xs) =
            f b :: (evalWord a xs).map f
          exact congrArg (List.cons (f b)) ih

def StarLine.mapAlphabet (L : StarLine α) (f : α → β) : StarLine β where
  word := mapLineWord f L.word
  hasParameter := by
    unfold mapLineWord
    apply List.mem_map.mpr
    exact ⟨LineSymbol.parameter, L.hasParameter, rfl⟩

@[simp] theorem StarLine.mapAlphabet_star
    (L : StarLine α) (f : α → β) :
    (L.mapAlphabet f).star = L.star.map f := by
  exact starPrefix_mapLineWord f L.word

@[simp] theorem StarLine.mapAlphabet_eval
    (L : StarLine α) (f : α → β) (a : α) :
    (L.mapAlphabet f).eval (f a) = (L.eval a).map f := by
  exact evalWord_mapLineWord f a L.word

/-- Starred Hales--Jewett is invariant under renaming of the alphabet. -/
theorem starHJ_equiv
    [Fintype α] [Fintype β] [Fintype κ]
    (e : α ≃ β)
    (h : StarHJ α κ) :
    StarHJ β κ := by
  intro colour
  let colour' : List α → κ := fun w => colour (w.map e)
  obtain ⟨L, hL⟩ := h colour'
  refine ⟨L.mapAlphabet e, ?_⟩
  intro b
  let a : α := e.symm b
  have hm := hL a
  change
    colour ((L.mapAlphabet e).eval b) =
      colour (L.mapAlphabet e).star
  have heb : e a = b := by
    simp [a]
  rw [← heb, L.mapAlphabet_eval, L.mapAlphabet_star]
  exact hm

end HalesJewett
end SuccessorTree
