import SuccessorTree.NonPrecompact.AffineParity

/-!
# Extending partial linear equivalences over a fixed quotient

This file formalises the elementary linear-extension lemma used in the
circulation part of the BANANA manuscript.

The main statement says that if two surjective linear maps from the same
finite-dimensional vector space to a common quotient agree along a partial
linear equivalence, then that partial equivalence extends to a global linear
automorphism intertwining the two quotient maps.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

section AmbientExtension

variable {K V V' : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']

/-- A linear equivalence between subspaces of equal-dimensional finite
vector spaces extends to a linear equivalence of the ambient spaces. -/
theorem exists_linearEquiv_extends_submoduleEquiv
    {W : Submodule K V} {W' : Submodule K V'}
    (f : W ≃ₗ[K] W')
    (hdim : finrank K V = finrank K V') :
    ∃ g : V ≃ₗ[K] V', ∀ x : W, g x = f x := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  let eQ : (W × Q) ≃ₗ[K] V := W.prodEquivOfIsCompl Q hQ
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl W'
  let eQ' : (W' × Q') ≃ₗ[K] V' := W'.prodEquivOfIsCompl Q' hQ'
  have hQdim : finrank K Q = finrank K Q' := by
    have hleft := eQ.finrank_eq
    have hright := eQ'.finrank_eq
    simp only [Module.finrank_prod] at hleft hright
    have hf := f.finrank_eq
    omega
  let fQ : Q ≃ₗ[K] Q' := LinearEquiv.ofFinrankEq Q Q' hQdim
  refine ⟨eQ.symm ≪≫ₗ LinearEquiv.prodCongr f fQ ≪≫ₗ eQ', ?_⟩
  intro x
  change eQ' (f x, fQ 0) = f x
  simp [eQ', fQ]

end AmbientExtension

end SuccessorTree.NonPrecompact
