import SuccessorTree.Counterexample.NowhereDense
import SuccessorTree.Counterexample.MaskCodes
import SuccessorTree.Counterexample.SupportRigidity

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
