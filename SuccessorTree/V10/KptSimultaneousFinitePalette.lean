import SuccessorTree.V10.KptRamseyApplications
import SuccessorTree.V10.GPlusBoundedPalette
import Mathlib.Tactic

/-!
# Theorem 6.26: simultaneous finite-palette shape homogeneity

The reviewed v10 proof uses repeated applications of the finite
shape-preserving Ramsey theorem to stabilize one colouring for each
member of the bounded representation palette.

There is a simpler exact formal consequence of the ALREADY VERIFIED
concrete Kpt shape Ramsey theorem: a finite family of finite
colourings can be combined into ONE product colouring with codomain
index -> colour. The function space is a finite type.

This file proves that single-step simultaneous homogeneity in the
actual normalized Kpt SM-tree, then applies it to the concrete
finite palette of q-tuples of genuine bounded Kpt representing pairs.
It does not postulate any new Ramsey theorem, extend relation arity
or infer the still-needed finite-approximation compatibility of the
palette colourings from envelope bounds.
-/

namespace SuccessorTree.V10

universe u v

/-- One concrete Kpt shape subspace makes ALL finitely many
finite-valued shape colourings homogeneous at once.
A single product colouring replaces repeated fusion. -/
theorem normalizedKpt_shapeRamsey_simultaneous
    {db du dd : Nat} {ι : Type u} {κ : Type v}
    [Fintype ι] [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (n k : Nat)
    (colour : ι →
      SuccessorTree.SMTree.AM (normalizedKptSMTree family) n k → κ) :
    ∃ W : SuccessorTree.SMTree.ShapeSubspace
      (normalizedKptSMTree family) n,
      ∀ (i : ι)
        (a b : SuccessorTree.SMTree.AM
          (normalizedKptSMTree family) n k),
        colour i ((normalizedKptSMTree family).shapeActK n k W a) =
        colour i ((normalizedKptSMTree family).shapeActK n k W b) := by
  classical
  let χ :
      SuccessorTree.SMTree.AM (normalizedKptSMTree family) n k →
        (ι → κ) := fun a i => colour i a
  obtain ⟨W,hHom⟩ :=
    normalizedKpt_shapeRamsey (κ := ι → κ) family n k χ
  refine ⟨W, ?_⟩
  intro i a b
  exact congrFun (hHom a b) i

/-- The actual coarse bounded G+ representation palette has a
FINITE type of indices, rather than a merely asserted finite set.
It may subsequently be restricted to order-preserving induced copies
of a specific finite input A without losing finiteness. -/
noncomputable def boundedGPlusPaletteIndices
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat) :=
  {f : Fin q → FiniteGPlusVertex family //
    f ∈ boundedGPlusTuplePalette family b q}

noncomputable instance boundedGPlusPaletteIndicesFintype
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat) :
    Fintype (boundedGPlusPaletteIndices family b q) := by
  classical
  unfold boundedGPlusPaletteIndices
  exact (boundedGPlusTuplePalette_finite family b q).fintype

/-- Instantiate simultaneous finite-colour homogeneity at the
ACTUAL bounded G+ tuple palette obtained from genuine Kpt pairs,
with no abstract finite-index assumption given by a caller. -/
theorem normalizedKpt_shapeRamsey_boundedGPlusPalette
    {db du dd : Nat} {κ : Type v}
    [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (b q n k : Nat)
    (colour : boundedGPlusPaletteIndices family b q →
      SuccessorTree.SMTree.AM
        (normalizedKptSMTree family) n k → κ) :
    ∃ W : SuccessorTree.SMTree.ShapeSubspace
      (normalizedKptSMTree family) n,
      ∀ (i : boundedGPlusPaletteIndices family b q)
        (a c : SuccessorTree.SMTree.AM
          (normalizedKptSMTree family) n k),
        colour i ((normalizedKptSMTree family).shapeActK n k W a) =
        colour i ((normalizedKptSMTree family).shapeActK n k W c) := by
  classical
  exact normalizedKpt_shapeRamsey_simultaneous family n k colour

end SuccessorTree.V10
