import SuccessorTree.V10.M2ImageOrdinaryZone
import Mathlib.Tactic

/-!
# Full lower socle comparison from a single selected image parameter

An actual ordinary parameter type at an image upper vertex contains the
complete induced record on the lower target socle. Its equality to the
prescribed target type therefore determines every low-low directed atom,
loop, unary and diagonal record even across target levels omitted by λ.
-/
namespace SuccessorTree.V10

/-- A complete ordinary image type determines every lower-socle L atom,
including both positive and negative records. -/
theorem image_ordinary_type_all_lower_atoms
    {N q db du dd : Nat}
    (Q : PartialTypeWithE N db du dd)
    (j : Nat) (hj : j < N)
    (hq : q ≤ N)
    (W : AgeTestModel db du dd) (w : Nat)
    (hType : (Q.ordinaryType j hj q hq).lReduct =
      RelationalPrefixType.ofAgeModel W q w) :
    (∀ (k l : Nat) (hk : k < q) (hl : l < q) (t : Fin db),
        Q.ageModel.binary k l t = W.binary k l t) ∧
    (∀ (k : Nat) (hk : k < q) (t : Fin du),
        Q.ageModel.unary k t = W.unary k t) ∧
    (∀ (k : Nat) (hk : k < q) (t : Fin dd),
        Q.ageModel.diagonal k t = W.diagonal k t) := by
  have hIndex (k : Nat) (hk : k < q) : k < N := lt_of_lt_of_le hk hq
  refine ⟨?_, ?_, ?_⟩
  · intro k l hk hl t
    have h := congrArg
      (fun R : RelationalPrefixType q db du dd =>
        R.binary (some ⟨k,hk⟩) (some ⟨l,hl⟩) t) hType
    simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
      RelationalPrefixType.ofAgeModel,typeAgeIndex,ordinaryTypeCoordinate,
      prefixVertexIndex,hIndex k hk,hIndex l hl] using h
  · intro k hk t
    have h := congrArg
      (fun R : RelationalPrefixType q db du dd =>
        R.unary (some ⟨k,hk⟩) t) hType
    simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
      RelationalPrefixType.ofAgeModel,typeAgeIndex,ordinaryTypeCoordinate,
      prefixVertexIndex,hIndex k hk] using h
  · intro k hk t
    have h := congrArg
      (fun R : RelationalPrefixType q db du dd =>
        R.diagonal (some ⟨k,hk⟩) t) hType
    simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
      RelationalPrefixType.ofAgeModel,typeAgeIndex,ordinaryTypeCoordinate,
      prefixVertexIndex,hIndex k hk] using h

end SuccessorTree.V10