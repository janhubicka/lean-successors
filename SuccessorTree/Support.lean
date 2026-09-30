import SuccessorTree.StarLine
import Mathlib.Data.Finset.Univ

/-!
# Support lemmas for the Hales--Jewett reduction

The successor-tree proof first fixes a word `s` containing every one-step
transition.  Hales--Jewett is then applied to the colouring of words *after*
this support prefix.  This file formalizes that bookkeeping.

The actual starred Hales--Jewett theorem is intentionally exposed as a single
hypothesis (`StarHJ`) for now.  The rest of the reduction is proved in Lean.
-/

namespace SuccessorTree

/-- A starred line is monochromatic for `colour` if all `L(a)` and `L(*)`
have the colour of `L(*)`. -/
def StarMonochromatic (colour : List α → κ) (L : StarLine α) : Prop :=
  ∀ a : α, colour (L.eval a) = colour L.star

/-- The exact combinatorial input needed by the successor-tree pigeonhole
argument.  A future milestone will prove this from a finite Hales--Jewett
formalization rather than assume it. -/
def StarHJ (α κ : Type*) [Fintype α] [Fintype κ] : Prop :=
  ∀ colour : List α → κ, ∃ L : StarLine α, StarMonochromatic colour L

/-- `s` is a support word if every letter occurs in it. -/
def Supports (s : List α) : Prop :=
  ∀ a : α, a ∈ s

/-- A finite type has a canonical finite support word containing every letter. -/
noncomputable def fullSupport (α : Type*) [Fintype α] : List α :=
  Finset.univ.toList

@[simp] theorem mem_fullSupport (α : Type*) [Fintype α] [DecidableEq α] (a : α) :
    a ∈ fullSupport α := by
  simp [fullSupport]

/-- With classical decidable equality, the canonical support really supports
all letters. -/
theorem supports_fullSupport (α : Type*) [Fintype α] : Supports (fullSupport α) := by
  classical
  intro a
  simp [fullSupport]

/-- Prepending support preserves HJ monochromaticity after translating the
colouring by the same fixed prefix. -/
theorem monochromatic_prepend
    (s : List α) (colour : List α → κ) (L : StarLine α)
    (h : StarMonochromatic (fun w => colour (s ++ w)) L) :
    StarMonochromatic colour (L.prepend s) := by
  intro a
  simpa [StarMonochromatic] using h a

/-- Every supported prefix remains inside the star-part of the resulting line.
This is the formal version of the paper's choice of a word `s` containing
all letters before applying Hales--Jewett. -/
theorem support_mem_star_prepend
    (s : List α) (L : StarLine α) (hs : Supports s) (a : α) :
    a ∈ (L.prepend s).star := by
  simp [hs a]

/-- Supported starred Hales--Jewett: from ordinary starred HJ we may demand in
addition that every alphabet letter already occurs before the first parameter.
-/
theorem supportedStarHJ
    [Fintype α] [Fintype κ]
    (hj : StarHJ α κ)
    (colour : List α → κ) :
    ∃ L : StarLine α,
      StarMonochromatic colour L ∧ Supports L.star := by
  classical
  let s := fullSupport α
  obtain ⟨L, hL⟩ := hj (fun w => colour (s ++ w))
  refine ⟨L.prepend s, monochromatic_prepend s colour L hL, ?_⟩
  intro a
  exact support_mem_star_prepend s L (supports_fullSupport α) a

end SuccessorTree
