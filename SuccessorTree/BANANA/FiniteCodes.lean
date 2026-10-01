import SuccessorTree.BANANA.TupleInvariant

namespace SuccessorTree.BANANA

/-- Coordinate code for a finite BANANA structure over F₂.  Choosing bases
on the two sides turns every finite bilinear pairing into exactly such a
code. -/
structure FinitePairingCode where
  leftDim : ℕ
  rightDim : ℕ
  pairing : Matrix (Fin leftDim) (Fin rightDim) F2

/-- Forget the wrapper and expose a finite pairing code as a dependent
sigma of its two dimensions and its matrix. -/
def FinitePairingCode.toSigma (A : FinitePairingCode) :
    Σ l : ℕ, Σ r : ℕ, Matrix (Fin l) (Fin r) F2 :=
  ⟨A.leftDim, A.rightDim, A.pairing⟩

theorem FinitePairingCode.toSigma_injective :
    Function.Injective FinitePairingCode.toSigma := by
  intro A B h
  cases A
  cases B
  cases h
  rfl

/-- There are only countably many finite BANANA coordinate codes. -/
instance finitePairingCode_countable : Countable FinitePairingCode :=
  Function.Injective.countable FinitePairingCode.toSigma
    FinitePairingCode.toSigma_injective

/-- With the two side dimensions fixed, there are only finitely many
bilinear pairings over F₂. -/
instance finite_pairing_matrices (l r : ℕ) :
    Finite (Matrix (Fin l) (Fin r) F2) := by
  infer_instance

end SuccessorTree.BANANA
