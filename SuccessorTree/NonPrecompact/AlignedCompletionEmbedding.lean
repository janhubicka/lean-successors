import SuccessorTree.NonPrecompact.Completion
import SuccessorTree.NonPrecompact.PerfectHomogeneity

/-!
# Aligning an embedded perfect completion with a prescribed source copy

In the coherent-EPPA proof, one first embeds the perfect completion of a
finite BANANA structure into the ambient perfect witness, then uses
homogeneity of the ambient perfect pairing so that the embedded completion
contains the original source via the prescribed inclusion.

This file packages that step directly in terms of embeddings.
-/

namespace SuccessorTree.NonPrecompact

namespace BananaMatrixStructure

/-- Given any embedding of the perfect completion of A into an ambient
standard perfect pairing and any prescribed embedding of A into that same
ambient pairing, one may postcompose the completion embedding by an ambient
automorphism so that its restriction to A becomes the prescribed embedding. -/
theorem exists_alignedCompletionEmbedding
    {l r n : ℕ}
    (A : BananaMatrixStructure l r)
    (j : BananaMatrixEmbedding A (perfectBanana n))
    (E₀ :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana n)) :
    ∃ E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana n),
      (∀ x,
        E.left (A.completionLeft x) = j.left x) ∧
      (∀ y,
        E.right (A.completionRight y) = j.right y) := by
  let e₀ : BananaMatrixEmbedding A (perfectBanana n) :=
    BananaMatrixEmbedding.comp E₀ A.completionEmbedding
  obtain ⟨H, hleft, hright⟩ :=
    exists_perfectPairAutomorphism_extends e₀ j
  let E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana n) :=
    BananaMatrixEmbedding.comp H E₀
  refine ⟨E, ?_, ?_⟩
  · intro x
    change H.left (E₀.left (A.completionLeft x)) = j.left x
    simpa [e₀, BananaMatrixEmbedding.comp] using hleft x
  · intro y
    change H.right (E₀.right (A.completionRight y)) = j.right y
    simpa [e₀, BananaMatrixEmbedding.comp] using hright y

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
