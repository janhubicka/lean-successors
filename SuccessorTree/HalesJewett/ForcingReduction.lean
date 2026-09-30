import SuccessorTree.HalesJewett.Composition
import SuccessorTree.Support

/-!
# From the forcing proposition to starred Hales--Jewett

This file verifies the final logical reduction in Hubička--Smolík's
combinatorial-forcing proof.

The only remaining forcing input is `LargeSetTheorem`: every large set of
finite words contains all finite evaluations of some subspace.  From this
single statement we prove:

* the binary infinite-dimensional Ramsey theorem;
* the finite-colour infinite-dimensional theorem, using the already verified
  refinement/composition induction;
* the starred one-dimensional Hales--Jewett theorem needed by the
  successor-tree pigeonhole proof.

Thus `StarHJ` is no longer an independent combinatorial black box once
`LargeSetTheorem` is established.
-/

namespace SuccessorTree
namespace HalesJewett

open Set

/-- Concrete largeness for words over `α`. -/
def WordLarge (A : Set (List α)) : Prop :=
  (subspaceAction α).Large A

/-- Proposition 1 of the combinatorial-forcing note. -/
def LargeSetTheorem (α : Type u) : Prop :=
  ∀ A : Set (List α), WordLarge A →
    ∃ W : Subspace α, ∀ v : List α, W.eval v ∈ A

/-- Proposition 1 implies the binary infinite-dimensional Ramsey theorem. -/
theorem binaryRamsey_of_largeSetTheorem
    (force : LargeSetTheorem α) :
    (subspaceAction α).BinaryRamsey := by
  let S := subspaceAction α
  intro colour
  let A₀ : Set (List α) := {w | colour w = false}
  let A₁ : Set (List α) := {w | colour w = true}
  have hpart : Set.univ = A₀ ∪ A₁ := by
    ext w
    cases h : colour w <;> simp [A₀, A₁, h]
  obtain ⟨W, hlarge | hlarge⟩ :=
    S.binary_partition_has_large_pullback A₀ A₁ hpart
  · obtain ⟨U, hU⟩ := force (S.pullback W A₀) hlarge
    refine ⟨S.comp W U, ?_⟩
    intro x y
    have hx := hU x
    have hy := hU y
    change colour (S.act W (S.act U x)) = false at hx
    change colour (S.act W (S.act U y)) = false at hy
    change colour (S.act (S.comp W U) x) =
      colour (S.act (S.comp W U) y)
    rw [S.act_comp, S.act_comp]
    exact hx.trans hy.symm
  · obtain ⟨U, hU⟩ := force (S.pullback W A₁) hlarge
    refine ⟨S.comp W U, ?_⟩
    intro x y
    have hx := hU x
    have hy := hU y
    change colour (S.act W (S.act U x)) = true at hx
    change colour (S.act W (S.act U y)) = true at hy
    change colour (S.act (S.comp W U) x) =
      colour (S.act (S.comp W U) y)
    rw [S.act_comp, S.act_comp]
    exact hx.trans hy.symm

/-- Proposition 1 implies the finite-colour infinite-dimensional theorem. -/
theorem finiteRamsey_of_largeSetTheorem
    [Fintype κ]
    (force : LargeSetTheorem α)
    (colour : List α → κ) :
    ∃ W : Subspace α, (subspaceAction α).Homogeneous colour W := by
  classical
  let S := subspaceAction α
  have hbin : S.BinaryRamsey :=
    binaryRamsey_of_largeSetTheorem force
  exact S.finiteRamsey_of_binary hbin colour

/-- The forcing proposition implies exactly the starred Hales--Jewett input
used by the successor-tree pigeonhole lemma. -/
theorem starHJ_of_largeSetTheorem
    [Fintype α] [Fintype κ]
    (force : LargeSetTheorem α) :
    StarHJ α κ := by
  classical
  intro colour
  obtain ⟨W, hW⟩ :=
    finiteRamsey_of_largeSetTheorem force colour
  refine ⟨W.firstLine, ?_⟩
  intro a
  rw [Subspace.firstLine_eval, Subspace.firstLine_star]
  have h := hW [a] []
  change colour (W.eval [a]) = colour (W.eval []) at h
  simpa using h

end HalesJewett
end SuccessorTree
