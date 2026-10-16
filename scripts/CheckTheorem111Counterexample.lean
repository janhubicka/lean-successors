import SuccessorTree.Counterexample.NowhereDense
import SuccessorTree.Counterexample.MaskCodes
import SuccessorTree.Counterexample.SupportRigidity
import SuccessorTree.Counterexample.Topology
import SuccessorTree.Counterexample.StretchHistory
import SuccessorTree.Counterexample.MarkedFusion

/-!
Exact-name audit: only the declarations below have been proved so far.
The Q_A infinite marker and antichain recursion are separate tasks.
-/

#check @SuccessorTree.SMTree.RightCompatible
#check @SuccessorTree.SMTree.PairwiseRightIncompatible
#check @SuccessorTree.SMTree.HasLateProperGaps
#check @SuccessorTree.SMTree.not_reduction_self_comp_of_not_surjective
#check @SuccessorTree.SMTree.incompatible_family_local_escape
#check @SuccessorTree.FreeAncestral.freeAncestral_hasLateProperGaps

#print axioms SuccessorTree.SMTree.not_reduction_self_comp_of_not_surjective
#print axioms SuccessorTree.SMTree.incompatible_family_local_escape
#print axioms SuccessorTree.FreeAncestral.freeAncestral_hasLateProperGaps

#check @SuccessorTree.FreeAncestral.remapCode_avoids_root
#check @SuccessorTree.FreeAncestral.rootMarkerCode_has_root
#check @SuccessorTree.FreeAncestral.remapTuple_injective
#check @SuccessorTree.FreeAncestral.remapCode_injective
#check @SuccessorTree.SMTree.compatible_marked_unique

#print axioms SuccessorTree.FreeAncestral.remapCode_avoids_root
#print axioms SuccessorTree.FreeAncestral.rootMarkerCode_has_root
#print axioms SuccessorTree.FreeAncestral.remapTuple_injective
#print axioms SuccessorTree.FreeAncestral.remapCode_injective
#print axioms SuccessorTree.SMTree.compatible_marked_unique

#check @SuccessorTree.SMTree.incompatible_family_isNowhereDense
#check @SuccessorTree.FreeAncestral.freeAncestral_incompatible_isNowhereDense
#print axioms SuccessorTree.SMTree.incompatible_family_isNowhereDense
#print axioms SuccessorTree.FreeAncestral.freeAncestral_incompatible_isNowhereDense

#check @SuccessorTree.FreeAncestral.appendRootMarkers
#check @SuccessorTree.FreeAncestral.prefix_appendRootMarkers
#check @SuccessorTree.FreeAncestral.appendRootMarkers_injective
#check @SuccessorTree.FreeAncestral.markedHistoryAux
#check @SuccessorTree.FreeAncestral.markedNode_level
#check @SuccessorTree.FreeAncestral.markedNode_root

#print axioms SuccessorTree.FreeAncestral.prefix_appendRootMarkers
#print axioms SuccessorTree.FreeAncestral.appendRootMarkers_injective
#print axioms SuccessorTree.FreeAncestral.markedNode_level
#print axioms SuccessorTree.FreeAncestral.markedNode_root

#check @SuccessorTree.FreeAncestral.markerGap
#check @SuccessorTree.FreeAncestral.markerGap_fixes_below
#check @SuccessorTree.FreeAncestral.markerBlock
#check @SuccessorTree.FreeAncestral.markerBlock_fixes_below
#check @SuccessorTree.FreeAncestral.markerBlock_level_above
#check @SuccessorTree.FreeAncestral.markedStage
#print axioms SuccessorTree.FreeAncestral.markerGap_fixes_below
#print axioms SuccessorTree.FreeAncestral.markerBlock_fixes_below
#print axioms SuccessorTree.FreeAncestral.markerBlock_level_above

#check @SuccessorTree.FreeAncestral.markedStage_level
#check @SuccessorTree.FreeAncestral.markedStage_fusionStable
#check @SuccessorTree.FreeAncestral.markedFusion
#check @SuccessorTree.FreeAncestral.markedFusion_level
#check @SuccessorTree.FreeAncestral.markedFusion_root
#print axioms SuccessorTree.FreeAncestral.markedStage_level
#print axioms SuccessorTree.FreeAncestral.markedStage_fusionStable
#print axioms SuccessorTree.FreeAncestral.markedFusion_level
#print axioms SuccessorTree.FreeAncestral.markedFusion_root
