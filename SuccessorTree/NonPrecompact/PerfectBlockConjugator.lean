import SuccessorTree.NonPrecompact.CompletionAmbientAction
import SuccessorTree.NonPrecompact.PerfectHomogeneity

/-!
# Conjugating a standard perfect block onto an embedded perfect subpair

The coherent-EPPA proof uses homogeneity of the ambient perfect pairing to
identify an embedded perfect completion with a standard coordinate block.
This file packages that interface.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- Canonical embedding of the first m coordinates of a standard perfect
pair into the first block of the ambient perfect pair. -/
def standardPerfectBlockEmbedding
    (m k : ℕ) :
    BananaMatrixEmbedding
      (perfectBanana m)
      (perfectBanana (m + k)) where
  left := directSumLeftInl (l₁ := m) (l₂ := k)
  right := directSumRightInl (r₁ := m) (r₂ := k)
  left_injective := directSumLeftInl_injective
  right_injective := directSumRightInl_injective
  pairing_apply := by
    intro x y
    simp only [perfectBanana_eval]
    change Fin.append x 0 ⬝ᵥ Fin.append y 0 = x ⬝ᵥ y
    rw [dotProduct_append]
    simp

@[simp] theorem standardPerfectBlockEmbedding_left
    (m k : ℕ) (x : Fin m → F2) :
    (standardPerfectBlockEmbedding m k).left x =
      Fin.append x 0 := rfl

@[simp] theorem standardPerfectBlockEmbedding_right
    (m k : ℕ) (y : Fin m → F2) :
    (standardPerfectBlockEmbedding m k).right y =
      Fin.append y 0 := rfl

/-- Any embedded copy of the smaller standard perfect pair in the ambient
one is the image of the standard first block under an ambient perfect-pair
automorphism. -/
theorem exists_standardPerfectBlock_conjugator
    {m k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana m)
        (perfectBanana (m + k))) :
    ∃ H :
      BananaMatrixEmbedding
        (perfectBanana (m + k))
        (perfectBanana (m + k)),
      (∀ x,
        H.left (Fin.append x 0) = E.left x) ∧
      (∀ y,
        H.right (Fin.append y 0) = E.right y) := by
  simpa [standardPerfectBlockEmbedding] using
    exists_perfectPairAutomorphism_extends
      (standardPerfectBlockEmbedding m k) E

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
