import SuccessorTree.Library.TypeRespecting

/-!
Exact transitive axiom audit of the intrinsic binary theorem and each
mathematical bridge used by the self-contained BRD-section corollary.
-/

#print axioms SuccessorTree.V10.TypeProfile.front_nonempty
#print axioms SuccessorTree.V10.CoherentTypeProfileMap.recovers_complete_record
#print axioms SuccessorTree.V10.CoherentTypeProfileMap.vertexMap_preserves_atoms
#print axioms SuccessorTree.V10.CoherentTypeProfileMap.vertexMap_freeLevel
#print axioms SuccessorTree.V10.CoherentTypeProfileMap.vertexType_transport
#print axioms SuccessorTree.V10.CoherentTypeProfileMap.preserves_full_type_equality
#print axioms SuccessorTree.V10.CoherentTypeProfileMap.preservesAge_of_shapeMap_restriction
#print axioms SuccessorTree.V10.FiniteTypeProfileMap.age_iff
#print axioms SuccessorTree.V10.FiniteTypeProfileMap.extend_front_once
#print axioms SuccessorTree.V10.FiniteTypeProfileMap.extends
#print axioms SuccessorTree.V10.FiniteTypeProfileMap.ofShapeMap
#print axioms SuccessorTree.V10.TypeRespectingEmbedding.restrictionEquiv
#print axioms SuccessorTree.V10.TypeRespectingEmbedding.act_comp
#print axioms SuccessorTree.V10.normalizedKpt_typeRespectingRamsey

/-- A downstream project needs only the narrow public import above. -/
example {db du dd : Nat}
    (family : List (SuccessorTree.V10.NormalizedForbidden db du dd))
    (A : SuccessorTree.V10.FiniteTypeBase family) {κ : Type*} [Fintype κ]
    (colour : SuccessorTree.V10.TypeRespectingEmbedding A → κ) :
    ∃ F : SuccessorTree.SMTree.MMap (SuccessorTree.V10.normalizedKptSMTree family),
      ∀ f g : SuccessorTree.V10.TypeRespectingEmbedding A,
        colour (SuccessorTree.V10.TypeRespectingEmbedding.act A F f) =
          colour (SuccessorTree.V10.TypeRespectingEmbedding.act A F g) :=
  SuccessorTree.V10.normalizedKpt_typeRespectingRamsey family A colour
