import SuccessorTree.V10.M2SourceTypeAge
import SuccessorTree.V10.ShapeMapParameterTransport
import Mathlib.Tactic

/-!
# Extract complete low/upper atom comparisons from one image parameter

A canonical parameter transported into a common image type gives the
*complete* induced L type of its actual image coordinate, through
all target positions below the common cut.  The following elementary
atom extraction covers both orientations, missing atoms, loops, unary
and diagonal facts, and is independent of M2 and forbidden-age tests.
-/
namespace SuccessorTree.V10

/-- Complete equality of the selected upper L type inside an ambient
partial-type socle transfers every low/upper atom to an external age
witness with the same upper L type. -/
theorem image_ordinary_type_all_low_upper_atoms
    {N q db du dd : Nat}
    (Q : PartialTypeWithE N db du dd)
    (j : Nat) (hj : j < N)
    (hq : q ≤ N)
    (W : AgeTestModel db du dd) (w : Nat)
    (hType : (Q.ordinaryType j hj q hq).lReduct =
      RelationalPrefixType.ofAgeModel W q w) :
    (∀ (k : Nat) (hk : k < q) (t : Fin db),
      Q.ageModel.binary k j t = W.binary k w t ∧
        Q.ageModel.binary j k t = W.binary w k t) ∧
    (∀ t : Fin db, Q.ageModel.binary j j t = W.binary w w t) ∧
    (∀ t : Fin du, Q.ageModel.unary j t = W.unary w t) ∧
    (∀ t : Fin dd, Q.ageModel.diagonal j t = W.diagonal w t) := by
  have hIndex (k : Nat) (hk : k < q) : k < N := lt_of_lt_of_le hk hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk t
    have hFwd := congrArg
      (fun R : RelationalPrefixType q db du dd =>
        R.binary (some ⟨k,hk⟩) none t) hType
    have hBack := congrArg
      (fun R : RelationalPrefixType q db du dd =>
        R.binary none (some ⟨k,hk⟩) t) hType
    constructor
    · simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
        RelationalPrefixType.ofAgeModel, typeAgeIndex,
        ordinaryTypeCoordinate,prefixVertexIndex,hIndex k hk,hj] using hFwd
    · simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
        RelationalPrefixType.ofAgeModel, typeAgeIndex,
        ordinaryTypeCoordinate,prefixVertexIndex,hIndex k hk,hj] using hBack
  · intro t
    have h := congrArg (fun R : RelationalPrefixType q db du dd =>
      R.binary none none t) hType
    simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
      RelationalPrefixType.ofAgeModel, typeAgeIndex,
      ordinaryTypeCoordinate,prefixVertexIndex,hj] using h
  · intro t
    have h := congrArg (fun R : RelationalPrefixType q db du dd =>
      R.unary none t) hType
    simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
      RelationalPrefixType.ofAgeModel, typeAgeIndex,
      ordinaryTypeCoordinate,prefixVertexIndex,hj] using h
  · intro t
    have h := congrArg (fun R : RelationalPrefixType q db du dd =>
      R.diagonal none t) hType
    simpa [PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
      RelationalPrefixType.ofAgeModel, typeAgeIndex,
      ordinaryTypeCoordinate,prefixVertexIndex,hj] using h

end SuccessorTree.V10