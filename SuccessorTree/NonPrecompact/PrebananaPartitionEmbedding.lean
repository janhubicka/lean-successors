import SuccessorTree.NonPrecompact.PrebananaCopyDegree

/-!
# Pre-BANANA embeddings from atom partitions

A unital Boolean-algebra embedding is determined by the nonempty blocks of
target atoms lying below the source atoms.  This file formalises the converse
used in the circulation residue-realisation proof: pairwise-disjoint nonempty
blocks covering all target atoms, with the correct marked-count parities,
define a pre-BANANA embedding.
-/

namespace SuccessorTree.NonPrecompact

/-- A partition of the target atom set into nonempty source-indexed blocks
with the prescribed marked parities defines a pre-BANANA embedding. -/
theorem exists_prebananaAtomEmbedding_of_blocks
    (A B : PrebananaAtomStructure)
    (block : Fin A.atomCount → Finset (Fin B.atomCount))
    (hnonempty : ∀ i, (block i).Nonempty)
    (hdisjoint :
      (Set.univ : Set (Fin A.atomCount)).PairwiseDisjoint block)
    (hcover :
      (Finset.univ : Finset (Fin A.atomCount)).biUnion block =
        Finset.univ)
    (hparity :
      ∀ i,
        (prebananaMarkedCount B.mark (block i) : F2) =
          A.mark i) :
    ∃ f : PrebananaAtomEmbedding A B,
      ∀ i, prebananaFiber f.part i = block i := by
  classical

  have hexists (x : Fin B.atomCount) :
      ∃ i : Fin A.atomCount, x ∈ block i := by
    have hx :
        x ∈ (Finset.univ : Finset (Fin A.atomCount)).biUnion block := by
      rw [hcover]
      simp
    rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
    exact ⟨i, hxi⟩

  let part : Fin B.atomCount → Fin A.atomCount :=
    fun x => Classical.choose (hexists x)

  have hpart_mem (x : Fin B.atomCount) :
      x ∈ block (part x) := by
    exact Classical.choose_spec (hexists x)

  have hfibre (i : Fin A.atomCount) :
      prebananaFiber part i = block i := by
    ext x
    simp only [prebananaFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hx
      rw [← hx]
      exact hpart_mem x
    · intro hx
      by_contra hne
      have hd :
          Disjoint (block (part x)) (block i) :=
        hdisjoint (Set.mem_univ _) (Set.mem_univ _) hne
      exact (Finset.disjoint_left.mp hd) (hpart_mem x) hx

  let f : PrebananaAtomEmbedding A B := {
    part := part
    fibre_nonempty := by
      intro i
      rw [hfibre i]
      exact hnonempty i
    fibre_mark_parity := by
      intro i
      rw [hfibre i]
      exact hparity i
  }

  refine ⟨f, ?_⟩
  intro i
  simpa [f] using hfibre i

end SuccessorTree.NonPrecompact
