import SuccessorTree.NonPrecompact.ConjugatedCompletionAction

/-!
# Coherent ambient action for a fixed embedded completion

For a fixed embedding E of a standard perfect completion into a larger
standard perfect witness, choose once and for all an ambient automorphism
carrying the standard first block onto E.  Conjugating the standard
completion-plus-identity action by this fixed choice gives a coherent
ambient action.

This is the finite algebraic homomorphism rho_U used in the BANANA coherent
EPPA proof.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- A fixed ambient conjugator carrying the standard first block onto the
chosen embedded perfect completion. -/
noncomputable def embeddedCompletionConjugator
    {m k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana m)
        (perfectBanana (m + k))) :
    BananaMatrixEmbedding
      (perfectBanana (m + k))
      (perfectBanana (m + k)) :=
  Classical.choose (exists_standardPerfectBlock_conjugator E)

/-- The chosen conjugator agrees with E on the left standard block. -/
theorem embeddedCompletionConjugator_left
    {m k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana m)
        (perfectBanana (m + k)))
    (z : Fin m → F2) :
    (embeddedCompletionConjugator E).left (Fin.append z 0) =
      E.left z := by
  exact (Classical.choose_spec
    (exists_standardPerfectBlock_conjugator E)).1 z

/-- The chosen conjugator agrees with E on the right standard block. -/
theorem embeddedCompletionConjugator_right
    {m k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana m)
        (perfectBanana (m + k)))
    (z : Fin m → F2) :
    (embeddedCompletionConjugator E).right (Fin.append z 0) =
      E.right z := by
  exact (Classical.choose_spec
    (exists_standardPerfectBlock_conjugator E)).2 z

/-- Ambient automorphism associated coherently with an automorphism of the
source whose perfect completion is the domain of E. -/
noncomputable def embeddedCompletionAmbientAutomorphism
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    BananaMatrixEmbedding
      (perfectBanana ((l + r) + k))
      (perfectBanana ((l + r) + k)) :=
  conjugatedCompletionAmbientAutomorphism
    (embeddedCompletionConjugator E) f g k

/-- The chosen ambient action restricts to the completion action on the
embedded left completion block. -/
theorem embeddedCompletionAmbientAutomorphism_left
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (z : Fin (l + r) → F2) :
    (embeddedCompletionAmbientAutomorphism E f g).left
        (E.left z) =
      E.left (completionLeftEquiv f g z) := by
  exact
    conjugatedCompletionAmbientAutomorphism_left_embedded
      E (embeddedCompletionConjugator E)
      (embeddedCompletionConjugator_left E) f g z

/-- The corresponding restriction statement on the right completion block. -/
theorem embeddedCompletionAmbientAutomorphism_right
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2))
    (z : Fin (l + r) → F2) :
    (embeddedCompletionAmbientAutomorphism E f g).right
        (E.right z) =
      E.right
        (dotContragredient (completionLeftEquiv f g) z) := by
  exact
    conjugatedCompletionAmbientAutomorphism_right_embedded
      E (embeddedCompletionConjugator E)
      (embeddedCompletionConjugator_right E) f g z

/-- The chosen coherent ambient action sends the identity to the identity on
the left sort. -/
theorem embeddedCompletionAmbientAutomorphism_refl_left
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k))) :
    (embeddedCompletionAmbientAutomorphism E
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2))).left =
      LinearMap.id := by
  exact conjugatedCompletionAmbientAutomorphism_refl_left
    (embeddedCompletionConjugator E)

/-- Identity law on the right sort. -/
theorem embeddedCompletionAmbientAutomorphism_refl_right
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k))) :
    (embeddedCompletionAmbientAutomorphism E
      (LinearEquiv.refl F2 (Fin l → F2))
      (LinearEquiv.refl F2 (Fin r → F2))).right =
      LinearMap.id := by
  exact conjugatedCompletionAmbientAutomorphism_refl_right
    (embeddedCompletionConjugator E)

/-- The chosen coherent ambient action preserves composition on the left
sort. -/
theorem embeddedCompletionAmbientAutomorphism_comp_left
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (embeddedCompletionAmbientAutomorphism E
      (f₁.trans f₂) (g₁.trans g₂)).left =
      (BananaMatrixEmbedding.comp
        (embeddedCompletionAmbientAutomorphism E f₂ g₂)
        (embeddedCompletionAmbientAutomorphism E f₁ g₁)).left := by
  exact conjugatedCompletionAmbientAutomorphism_comp_left
    (embeddedCompletionConjugator E) f₁ f₂ g₁ g₂

/-- The chosen coherent ambient action preserves composition on the right
sort. -/
theorem embeddedCompletionAmbientAutomorphism_comp_right
    {l r k : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)))
    (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
    (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)) :
    (embeddedCompletionAmbientAutomorphism E
      (f₁.trans f₂) (g₁.trans g₂)).right =
      (BananaMatrixEmbedding.comp
        (embeddedCompletionAmbientAutomorphism E f₂ g₂)
        (embeddedCompletionAmbientAutomorphism E f₁ g₁)).right := by
  exact conjugatedCompletionAmbientAutomorphism_comp_right
    (embeddedCompletionConjugator E) f₁ f₂ g₁ g₂

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
