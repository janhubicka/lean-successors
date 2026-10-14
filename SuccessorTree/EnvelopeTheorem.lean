import SuccessorTree.EnvelopeRunExistence

/-!
# Section 5: minimal envelopes

This packages the already proved existence, height, finite-prefix minimality,
and independence statements. The hypothesis on a top-level member is
intentional: Algorithm 5.4 treats the empty set separately, with height zero.

The one-level pullback condition is the only extra assumption in this layer.
It is not built into the definition of an SM-tree, which matters if the
successor-tree axioms are weakened later.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- The nonempty case of Proposition 5.5, with both finite and total
competitors. The assertions on the two choices of a run are distinct:
agreement of interesting levels alone does not imply agreement of embedding
types. -/
theorem exists_minimalEnvelope
    (H : SMTree S)
    (hE1 : OneLevelPullback H)
    (X : Set T) (ell : Nat)
    (hXbound : X ⊆ levelLe ell)
    (hTop : ∃ x ∈ X, LevelTree.lev x = ell) :
    ∃ R : AlgorithmRun H X ell, ∃ m : Nat,
      IsPrefixEnvelope (R.F 0).map m X ∧
      R.selectedLevels.card = m ∧
      (∀ (E : MMap H) (m' : Nat),
        IsPrefixEnvelope E.map m' X → m ≤ m') ∧
      (∀ (m' : Nat) (a : AM H 0 m'),
        IsAMEnvelope H a X → m ≤ m') ∧
      (∀ R' : AlgorithmRun H X ell,
        R.I 0 = R'.I 0 ∧
        (R.F 0).map ⁻¹' X = (R'.F 0).map ⁻¹' X) := by
  let R : AlgorithmRun H X ell := canonicalAlgorithmRun H X ell
  obtain ⟨m, hEnv, hCard, hMin⟩ :=
    R.minimal_output_height hE1 hXbound hTop
  refine ⟨R, m, hEnv, hCard, hMin, ?_, ?_⟩
  · intro m' a ha
    exact hMin (a.representative H) m' ha
  · intro R'
    exact ⟨R.I_eq R' 0 (Nat.zero_le ell),
      R.embeddingType_eq R' hE1 hXbound 0 (Nat.zero_le ell)⟩

end Envelope
end SMTree
end SuccessorTree
