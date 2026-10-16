import SuccessorTree.Counterexample.NowhereDense

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
