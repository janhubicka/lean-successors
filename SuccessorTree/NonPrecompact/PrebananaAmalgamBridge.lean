import SuccessorTree.NonPrecompact.PrebananaPartitionEmbedding
import SuccessorTree.NonPrecompact.ParityStarMatrix
import SuccessorTree.NonPrecompact.FiberProductStrong
import SuccessorTree.NonPrecompact.QuadraticGauss

/-!
# Bridges for the pre-BANANA atom amalgam

The atom-coordinate embedding API records marking preservation using the
parity of the number of marked target atoms in each fibre.  The parity-matrix
amalgam is more naturally stated using F₂-sums of the mark function.

This file identifies those formulations and records that the partition map
of every atom embedding is surjective.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Modulo two, the number of marked atoms in a finite set is the sum of
their F₂ marks. -/
theorem prebananaMarkedCount_cast_eq_sum
    {n : ℕ}
    (mark : Fin n → F2)
    (s : Finset (Fin n)) :
    (prebananaMarkedCount mark s : F2) =
      ∑ i ∈ s, mark i := by
  classical
  unfold prebananaMarkedCount
  calc
    ((s.filter fun i => mark i = 1).card : F2) =
        ∑ i ∈ s, if mark i = 1 then 1 else 0 := by
      symm
      exact Finset.sum_boole (R := F2) (fun i => mark i = 1) s
    _ = ∑ i ∈ s, mark i := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases f2_eq_zero_or_one (mark i) with h0 | h1
      · simp [h0]
      · simp [h1]

/-- The atom-partition map underlying a pre-BANANA embedding is surjective:
every source atom has a nonempty target fibre. -/
theorem PrebananaAtomEmbedding.part_surjective
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B) :
    Function.Surjective f.part := by
  intro a
  obtain ⟨b, hb⟩ := f.fibre_nonempty a
  refine ⟨b, ?_⟩
  simpa [prebananaFiber] using
    (Finset.mem_filter.mp hb).2

/-- Marking preservation for an atom embedding, rewritten as an F₂-sum over
the finite fibre. -/
theorem PrebananaAtomEmbedding.sum_mark_fibre
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (a : Fin A.atomCount) :
    (∑ b ∈ prebananaFiber f.part a, B.mark b) = A.mark a := by
  rw [← prebananaMarkedCount_cast_eq_sum]
  exact f.fibre_mark_parity a

end SuccessorTree.NonPrecompact
