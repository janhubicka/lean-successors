import SuccessorTree.Library
import SuccessorTree.Library.Structures

/-!
Compile-time smoke test of the theorem-facing library import.
The existing independent checker suites perform exact transitive
axiom reports; do not duplicate hundreds of V10 axiom checks here.
-/

#check @SuccessorTree.LevelTree
#check @SuccessorTree.STree
#check @SuccessorTree.ShapeMap
#check @SuccessorTree.SMTree
#check @SuccessorTree.FiniteCopySystem
#check @SuccessorTree.RamseyExpansion
#check @SuccessorTree.IntrinsicEvent

#check @SuccessorTree.HalesJewett.starHJ_finite
#check @SuccessorTree.RamseyExpansion.copyRamseyDegreeLE_card_expansionTypes
#check @SuccessorTree.ShapeMap.mapEvent_injective

#check @SuccessorTree.SMTree.shapePreservingRamsey
#check @SuccessorTree.SMTree.shapePreservingRamsey_viaFatEllentuck
#check @SuccessorTree.SMTree.shapeRamsey_bounded
#check @SuccessorTree.SMTree.shapeRamsey_exact
#check @SuccessorTree.SMTree.FatTree.fatTreeA4
#check @SuccessorTree.SMTree.FatTree.fatTreeEllentuck
#check @SuccessorTree.SMTree.Envelope.exists_minimalEnvelope

#check @SuccessorTree.V10.normalizedKptSMTree
#check @SuccessorTree.V10.normalizedKpt_oneLevelPullback
#check @SuccessorTree.V10.normalizedKpt_oneLevelPullback_for_envelopes
#check @SuccessorTree.V10.numericH_actualRun_uniform_sharp_envelope_bound
#check @SuccessorTree.V10.canonicalNormalizedGOmega_bigRamsey
#check @SuccessorTree.V10.originalBinaryUnary_GOmega_allEmbeddings_bigRamsey_bound
#check @SuccessorTree.V10.universalNormalizedModel_bigRamsey_bound
#check @SuccessorTree.V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound

#check @SuccessorTree.FreeAncestral.finiteShapeRamsey
