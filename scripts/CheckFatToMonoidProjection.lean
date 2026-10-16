import SuccessorTree.FatTree.ProjectionTransfer

/-!
Adversarial named-axiom checkpoints on actual proved parts
of the original Section 4 projection. The unresolved forward
and relative-lifting clauses are Prop-valued obligations, not
proved theorems or new constants.
-/

#check @SuccessorTree.SMTree.FatTree.ProjectionRespectsReduction
#check @SuccessorTree.SMTree.FatTree.ProjectionLiftsCompatibleTargets
#print axioms SuccessorTree.SMTree.FatTree.projection_surjective
#print axioms SuccessorTree.SMTree.FatTree.partialMap_eq_of_common_prefix
#print axioms SuccessorTree.SMTree.FatTree.projectionRespectsPrefixes
#print axioms SuccessorTree.SMTree.FatTree.projectedDepthCone_of_compatibility
