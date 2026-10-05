import SuccessorTree.FatTree.A4Coverage
import SuccessorTree.FatTree.A4ReplaySemantics
import SuccessorTree.FatTree.A4Assembly

/-!
The coverage and replay lemmas are unconditional structural results.
The last three reports are CONDITIONAL on `FixedStemPigeonhole`.
Printing their complete types makes that remaining obligation visible;
standard transitive axioms alone must not be mistaken for a proof of A4.
-/

open SuccessorTree.SMTree.FatTree

#check oneBlock_mem_of_all_fixedTraceGoodRows
#check duplicate_replay_from_repeated_edge
#check ProfileCollector.reachable_state_mono
#check ProfileCollector.original_occurrence_endpoint_below
#check rowExtension_duplicate_recorded_edge
#check ProfileReplayState.replayLetter_rule_from_original
#check FixedStemPigeonhole
#check typed_pigeonhole_of_fixedStem
#check ramseySpaceOfFixedStemPigeonhole
#check ellentuck_of_fixedStemPigeonhole

#print axioms oneBlock_mem_of_all_fixedTraceGoodRows
#print axioms duplicate_replay_from_repeated_edge
#print axioms ProfileCollector.reachable_state_mono
#print axioms ProfileCollector.original_occurrence_endpoint_below
#print axioms rowExtension_duplicate_recorded_edge
#print axioms ProfileReplayState.replayLetter_rule_from_original
#print axioms typed_pigeonhole_of_fixedStem
#print axioms ramseySpaceOfFixedStemPigeonhole
#print axioms ellentuck_of_fixedStemPigeonhole
