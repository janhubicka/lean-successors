import Mathlib.Data.Set.Basic

/-!
# Combinatorial-forcing core for Hales--Jewett

This file begins the verification of Hubička--Smolík,
*Hales--Jewett by combinatorial forcing*.

At this stage we isolate only the algebra of substitution used throughout
Section 2 of the note.  A `SubspaceAction` consists of words, subspaces,
an identity subspace, composition of subspaces, and evaluation of a subspace
on a finite word.  The essential law is

`(W.comp U).act v = W.act (U.act v)`,

which is the formal version of `W(U)(v) = W(U(v))`.

The first two forcing observations from the note are then proved with no
additional combinatorics.  A later file will instantiate this interface by
the concrete variable-word representation.
-/

namespace SuccessorTree.HalesJewett

/-- Algebraic interface for substitution of finite words into infinite
variable-word subspaces. -/
structure SubspaceAction (Word : Type u) (Space : Type v) where
  act : Space → Word → Word
  id : Space
  comp : Space → Space → Space
  act_id : ∀ w : Word, act id w = w
  act_comp : ∀ W U : Space, ∀ w : Word,
    act (comp W U) w = act W (act U w)

namespace SubspaceAction

variable {Word : Type u} {Space : Type v}
variable (S : SubspaceAction Word Space)

/-- Pull a set of words back through a subspace. -/
def pullback (W : Space) (A : Set Word) : Set Word :=
  {w | S.act W w ∈ A}

/-- A set is large if every subspace has an evaluation in the set. -/
def Large (A : Set Word) : Prop :=
  ∀ W : Space, ∃ w : Word, S.act W w ∈ A

/-- A subspace avoids a set if none of its finite evaluations lies in it. -/
def Avoids (W : Space) (A : Set Word) : Prop :=
  ∀ w : Word, S.act W w ∉ A

/-- The whole word space is large as soon as there is at least one word. -/
theorem large_univ [Nonempty Word] : S.Large Set.univ := by
  intro W
  obtain ⟨w⟩ := ‹Nonempty Word›
  exact ⟨w, Set.mem_univ _⟩

/-- Largeness is preserved by pulling back along a subspace.

This is Observation 1 in the combinatorial-forcing note.
-/
theorem large_pullback {A : Set Word} (hA : S.Large A) (W : Space) :
    S.Large (S.pullback W A) := by
  intro U
  obtain ⟨w, hw⟩ := hA (S.comp W U)
  refine ⟨S.act U w, ?_⟩
  change S.act W (S.act U w) ∈ A
  simpa only [← S.act_comp W U w] using hw

/-- Failure of largeness is exactly witnessed by an avoiding subspace. -/
theorem not_large_iff_exists_avoids (A : Set Word) :
    ¬ S.Large A ↔ ∃ W : Space, S.Avoids W A := by
  classical
  simp only [Large, Avoids, not_forall, not_exists, not_not]

/-- If two sets cover all words, then after passing to a subspace one of the
two pullbacks is large.

This is Observation 2 in the corrected combinatorial-forcing note.  The proof
makes explicit the point that, if the first cell is not large, an avoiding
subspace sends *every* word into the second cell.
-/
theorem binary_cover_has_large_pullback [Nonempty Word]
    (A₀ A₁ : Set Word)
    (cover : Set.univ ⊆ A₀ ∪ A₁) :
    ∃ W : Space, S.Large (S.pullback W A₀) ∨ S.Large (S.pullback W A₁) := by
  classical
  by_cases h₀ : S.Large A₀
  · refine ⟨S.id, Or.inl ?_⟩
    intro U
    obtain ⟨w, hw⟩ := h₀ U
    refine ⟨w, ?_⟩
    change S.act S.id (S.act U w) ∈ A₀
    simpa only [S.act_id] using hw
  · obtain ⟨W, hW⟩ := (S.not_large_iff_exists_avoids A₀).mp h₀
    refine ⟨W, Or.inr ?_⟩
    intro U
    obtain ⟨w⟩ := ‹Nonempty Word›
    refine ⟨w, ?_⟩
    change S.act W (S.act U w) ∈ A₁
    have hcover : S.act W (S.act U w) ∈ A₀ ∪ A₁ :=
      cover (Set.mem_univ _)
    rcases hcover with hA₀ | hA₁
    · exact False.elim (hW (S.act U w) hA₀)
    · exact hA₁

/-- Partition formulation matching the note literally. -/
theorem binary_partition_has_large_pullback [Nonempty Word]
    (A₀ A₁ : Set Word)
    (partition : Set.univ = A₀ ∪ A₁) :
    ∃ W : Space, S.Large (S.pullback W A₀) ∨ S.Large (S.pullback W A₁) := by
  apply S.binary_cover_has_large_pullback A₀ A₁
  simpa [partition]

end SubspaceAction

end SuccessorTree.HalesJewett
