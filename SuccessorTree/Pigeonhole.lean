import SuccessorTree.Support
import SuccessorTree.HalesJewett.AlphabetInduction

/-!
# The Hales--Jewett core of the one-dimensional pigeonhole lemma

This file formalizes the combinatorial skeleton of Lemma `pigeonhole1` from
Section 3.1 of the successor-tree paper.

The tree-specific part of the paper constructs, from a supported starred line
`L`, a two-level approximation `h` by duplicating the transition recorded at
the first parameter and replaying constants from earlier support positions.
The equations

* `h ∘ Id = g_{L(*)}`,
* `h ∘ e = g_{L(e)}`

are exactly what the structure `ReplaySystem` records.  Once those equations
are available, the pigeonhole conclusion is a direct formal consequence of
supported starred Hales--Jewett.

A subsequent milestone will instantiate `ReplaySystem` from the paper's
`(S,M)`-tree axioms (in particular M3 duplication), eliminating this interface
hypothesis.
-/

namespace SuccessorTree

/-- The two possible inputs to the one-dimensional line: `base` is the
identity restriction, while `letter e` is a genuine one-step transition. -/
inductive LineInput (Γ : Type u) where
  | base : LineInput Γ
  | letter : Γ → LineInput Γ
  deriving Repr

/-- Abstract interface capturing precisely the replay equations established by
M3 in the paper's proof of the one-dimensional pigeonhole lemma. -/
structure ReplaySystem (Γ : Type u) (Approx : Type v) (Block : Type w) where
  /-- The recursively built approximation `g_w`. -/
  wordApprox : List Γ → Approx
  /-- Apply a two-level block to either the identity input or a one-step letter. -/
  apply : Block → LineInput Γ → Approx
  /-- Build the replay block from a line whose star prefix contains every letter. -/
  replay : (L : StarLine Γ) → Supports L.star → Block
  replay_base : ∀ (L : StarLine Γ) (hL : Supports L.star),
    apply (replay L hL) LineInput.base = wordApprox L.star
  replay_letter : ∀ (L : StarLine Γ) (hL : Supports L.star) (e : Γ),
    apply (replay L hL) (LineInput.letter e) = wordApprox (L.eval e)

namespace ReplaySystem

/-- Every member of the replayed one-dimensional line gets the same colour.
This is the formal Hales--Jewett step of the successor-tree pigeonhole proof. -/
theorem oneDimensionalPigeonhole
    [Fintype Γ] [Fintype κ]
    (sys : ReplaySystem Γ Approx Block)
    (hj : StarHJ Γ κ)
    (colour : Approx → κ) :
    ∃ h : Block, ∀ x : LineInput Γ,
      colour (sys.apply h x) = colour (sys.apply h LineInput.base) := by
  obtain ⟨L, hmono, hsupp⟩ :=
    supportedStarHJ hj (fun w => colour (sys.wordApprox w))
  let h := sys.replay L hsupp
  refine ⟨h, ?_⟩
  intro x
  cases x with
  | base => rfl
  | letter e =>
      rw [show sys.apply h (LineInput.letter e) = sys.wordApprox (L.eval e) by
        exact sys.replay_letter L hsupp e]
      rw [show sys.apply h LineInput.base = sys.wordApprox L.star by
        exact sys.replay_base L hsupp]
      exact hmono e

/-- The one-dimensional successor-tree pigeonhole theorem with the
Hales--Jewett input fully discharged.  The only remaining interface is the
tree-specific replay system, which will later be instantiated from M3. -/
theorem oneDimensionalPigeonhole_finite
    [Fintype Γ] [Fintype κ]
    (sys : ReplaySystem Γ Approx Block)
    (colour : Approx → κ) :
    ∃ h : Block, ∀ x : LineInput Γ,
      colour (sys.apply h x) = colour (sys.apply h LineInput.base) := by
  exact sys.oneDimensionalPigeonhole
    (HalesJewett.starHJ_finite (α := Γ) (κ := κ)) colour

/-- Equivalent pairwise formulation of the monochromatic line conclusion. -/
theorem oneDimensionalPigeonhole_pairwise
    [Fintype Γ] [Fintype κ]
    (sys : ReplaySystem Γ Approx Block)
    (hj : StarHJ Γ κ)
    (colour : Approx → κ) :
    ∃ h : Block, ∀ x y : LineInput Γ,
      colour (sys.apply h x) = colour (sys.apply h y) := by
  obtain ⟨h, hh⟩ := sys.oneDimensionalPigeonhole hj colour
  refine ⟨h, ?_⟩
  intro x y
  exact (hh x).trans (hh y).symm

/-- Pairwise form with Hales--Jewett fully discharged. -/
theorem oneDimensionalPigeonhole_pairwise_finite
    [Fintype Γ] [Fintype κ]
    (sys : ReplaySystem Γ Approx Block)
    (colour : Approx → κ) :
    ∃ h : Block, ∀ x y : LineInput Γ,
      colour (sys.apply h x) = colour (sys.apply h y) := by
  obtain ⟨h, hh⟩ := sys.oneDimensionalPigeonhole_finite colour
  refine ⟨h, ?_⟩
  intro x y
  exact (hh x).trans (hh y).symm

end ReplaySystem

end SuccessorTree
