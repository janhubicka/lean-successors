import SuccessorTree.Counterexample.BinarySupports
import SuccessorTree.Counterexample.GreedySelection

/-! Axiom audit of the completely explicit ZFC almost-disjoint support family. -/

#check @SuccessorTree.Counterexample.prefixBits_lt_pow
#check @SuccessorTree.Counterexample.branchLevel_zero
#check @SuccessorTree.Counterexample.branchLevel_strictMono
#check @SuccessorTree.Counterexample.branchLevel_index_eq
#check @SuccessorTree.Counterexample.prefixBits_eq_implies_prefix
#check @SuccessorTree.Counterexample.branchLevel_almostDisjoint

#print axioms SuccessorTree.Counterexample.prefixBits_lt_pow
#print axioms SuccessorTree.Counterexample.branchLevel_zero
#print axioms SuccessorTree.Counterexample.branchLevel_strictMono
#print axioms SuccessorTree.Counterexample.branchLevel_index_eq
#print axioms SuccessorTree.Counterexample.prefixBits_eq_implies_prefix
#print axioms SuccessorTree.Counterexample.branchLevel_almostDisjoint

#check @SuccessorTree.Counterexample.exists_candidate_avoiding
#check @SuccessorTree.Counterexample.greedySelection
#check @SuccessorTree.Counterexample.greedySelection_step
#check @SuccessorTree.Counterexample.greedySelection_avoids_earlier
#check @SuccessorTree.Counterexample.greedySelection_is_candidate
#check @SuccessorTree.Counterexample.greedySelection_pairwise

#print axioms SuccessorTree.Counterexample.exists_candidate_avoiding
#print axioms SuccessorTree.Counterexample.greedySelection_step
#print axioms SuccessorTree.Counterexample.greedySelection_avoids_earlier
#print axioms SuccessorTree.Counterexample.greedySelection_is_candidate
#print axioms SuccessorTree.Counterexample.greedySelection_pairwise

#check @SuccessorTree.Counterexample.no_embedding_earlier_of_minimal_ord
#print axioms SuccessorTree.Counterexample.no_embedding_earlier_of_minimal_ord
