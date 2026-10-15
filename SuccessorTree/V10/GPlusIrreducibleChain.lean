import SuccessorTree.V10.GPlusAtomicRelations
import SuccessorTree.V10.I3FullForbiddenRelocation
import Mathlib.Tactic

/-!
# Lemma 6.41: irreducible L-copies in G+ live on one prefix chain

By Definition 6.40 all directed off-diagonal L-atoms between
two G+ vertices are absent unless they are comparable in
the finite partial-code prefix order.

For a finite irreducible forbidden L-pattern F, any pair of
distinct vertices has at least one positive directed binary
atom in one orientation. If the complete induced binary data
of a candidate copy agrees with F, the corresponding G+
vertices must therefore be prefix-comparable.

If the embedding respects the G-omega enumeration ordered by
increasing finite-structure size, the smaller-pattern index
maps to a *proper prefix* of the larger-pattern index.
Consequently all the chosen vertices form a single chain
below the final (largest-size) partial structure.

The remaining Lemma 6.41 step is to transport the WHOLE
induced unary/diagonal/directed binary record along these
prefixes into that final valid partial structure and obtain
the forbidden-age contradiction. No such conclusion is
assumed in this file.
-/

namespace SuccessorTree.V10

/-- Irreducibility and full induced binary agreement force
every two distinct candidate G+ vertices to be comparable
by the actual strict finite-code prefix relation. -/
theorem finiteGPlus_irreducible_copy_pairwise_comparable
    {r db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible)
    (f : Fin r → FiniteGPlusVertex family)
    (hBinary : ∀ a b : Fin r, a ≠ b →
      ∀ bit : Fin db,
        finiteGPlusBinary (f a) (f b) bit =
          F.binary a b bit) :
    ∀ a b : Fin r, a ≠ b →
      (f a).IsProperPrefix (f b) ∨
        (f b).IsProperPrefix (f a) := by
  intro a b hab
  obtain ⟨bit,hPositive⟩ := hIrred a b hab
  rcases hPositive with hAB | hBA
  · apply finiteGPlusBinary_true_implies_comparable (f a) (f b) bit
    rw [hBinary a b hab bit]
    exact hAB
  · have hCmp :=
      finiteGPlusBinary_true_implies_comparable
        (f b) (f a) bit
        (by rw [hBinary b a hab.symm bit]; exact hBA)
    rcases hCmp with hBA | hAB
    · exact Or.inr hBA
    · exact Or.inl hAB

/-- When an enumeration respects strictly increasing sizes,
the irreducible forbidden-copy indices follow strictly
increasing G+ prefix levels. -/
theorem finiteGPlus_irreducible_copy_prefix_mono
    {r db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible)
    (f : Fin r → FiniteGPlusVertex family)
    (hSize : StrictMono (fun a : Fin r => (f a).val.size))
    (hBinary : ∀ a b : Fin r, a ≠ b →
      ∀ bit : Fin db,
        finiteGPlusBinary (f a) (f b) bit =
          F.binary a b bit) :
    ∀ a b : Fin r, a < b →
      (f a).IsProperPrefix (f b) := by
  intro a b hab
  have hne : a ≠ b := ne_of_lt hab
  obtain hAB | hBA :=
    finiteGPlus_irreducible_copy_pairwise_comparable
      F hIrred f hBinary a b hne
  · exact hAB
  · have hIncrease : (f a).val.size < (f b).val.size :=
      hSize hab
    have hReverse := hBA.2
    omega

/-- Every vertex of a nonempty irreducible candidate
lies below its LAST vertex, so one valid finite partial
structure contains the whole candidate's atomic support. -/
theorem finiteGPlus_irreducible_copy_prefix_top
    {r db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (F : ForbiddenAtomicPattern r db du dd)
    (hIrred : F.Irreducible)
    (f : Fin r → FiniteGPlusVertex family)
    (hr : 0 < r)
    (hSize : StrictMono (fun a : Fin r => (f a).val.size))
    (hBinary : ∀ a b : Fin r, a ≠ b →
      ∀ bit : Fin db,
        finiteGPlusBinary (f a) (f b) bit =
          F.binary a b bit) :
    ∀ a : Fin r,
      (f a).val.IsPrefix
        (f (⟨r-1,by omega⟩ : Fin r)).val := by
  intro a
  let last : Fin r := ⟨r-1,by omega⟩
  by_cases ha : a = last
  · rw [ha]
    exact FinitePartialCode.isPrefix_refl _
  · have hlt : a < last := by
      have haBound : a.val < r := a.isLt
      have haNe : a.val ≠ r-1 := by
        intro hEq
        apply ha
        apply Fin.ext
        exact hEq
      apply Fin.lt_def.mpr
      change a.val < r-1
      omega
    exact (finiteGPlus_irreducible_copy_prefix_mono
      F hIrred f hSize hBinary a last hlt).1

end SuccessorTree.V10
