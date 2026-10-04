import SuccessorTree.NonPrecompact.PrebananaPartitionEmbedding
import SuccessorTree.NonPrecompact.PrebananaResidueRealisation

/-!
# Standard all-marked ambients for pre-BANANA residue realisation

The circulation residue-realisation proof uses an all-marked finite
pre-BANANA structure with (m - 1) * q + 2 atoms, where q = 2^(k+1).
This file formalises that this standard atom-coordinate structure belongs
to the pre-BANANA class: its atom set is nonempty and its total marking
parity is zero.
-/

namespace SuccessorTree.NonPrecompact

/-- The all-marked standard-coordinate structure used in finite residue
realisation.  Its number of atoms is (m - 1) * 2^(k+1) + 2. -/
def prebananaResidueAmbient (m k : ℕ) : PrebananaAtomStructure where
  atomCount := (m - 1) * 2 ^ (k + 1) + 2
  atomCount_pos := by positivity
  mark := fun _ => 1
  total_mark_parity := by
    simp [prebananaMarkedCount, pow_succ]

@[simp] theorem prebananaResidueAmbient_atomCount
    (m k : ℕ) :
    (prebananaResidueAmbient m k).atomCount =
      (m - 1) * 2 ^ (k + 1) + 2 := rfl

@[simp] theorem prebananaResidueAmbient_mark
    (m k : ℕ)
    (i : Fin (prebananaResidueAmbient m k).atomCount) :
    (prebananaResidueAmbient m k).mark i = 1 := rfl

/-- The ambient atom count is even, matching the manuscript's reason that
the all-marked structure is a pre-BANANA member. -/
theorem prebananaResidueAmbient_atomCount_even
    (m k : ℕ) :
    Even (prebananaResidueAmbient m k).atomCount := by
  rw [prebananaResidueAmbient_atomCount]
  refine Even.add ?_ even_two
  exact Even.mul_right (even_two.pow_of_ne_zero (Nat.succ_ne_zero k)) (m - 1)

end SuccessorTree.NonPrecompact
