import SuccessorTree.FatTree.A4Coverage
import SuccessorTree.FatTree.A4ReplaySemantics
import SuccessorTree.FatTree.A4Assembly

/-!
The coverage and replay lemmas are unconditional structural results.
The last three reports deliberately audit the conditional assembly interface:
`A4Assembly` keeps `FixedStemPigeonhole` explicit so A3 transfer can be
checked independently.  `A4ReviewComplete` discharges that premise
unconditionally and is audited separately.
-/

open SuccessorTree.SMTree.FatTree

#check oneBlock_mem_of_all_fixedTraceGoodRows_of_sourceLetter
#check duplicate_replay_from_repeated_edge
#check ProfileCollector.reachable_state_mono
#check ProfileCollector.original_occurrence_endpoint_below
#check rowExtension_duplicate_recorded_edge
#check ProfileReplayState.replayLetter_rule_from_original
#check FixedStemPigeonhole
#check typed_pigeonhole_of_fixedStem
#check ramseySpaceOfFixedStemPigeonhole
#check ellentuck_of_fixedStemPigeonhole

#print axioms oneBlock_mem_of_all_fixedTraceGoodRows_of_sourceLetter
#print axioms duplicate_replay_from_repeated_edge
#print axioms ProfileCollector.reachable_state_mono
#print axioms ProfileCollector.original_occurrence_endpoint_below
#print axioms rowExtension_duplicate_recorded_edge
#print axioms ProfileReplayState.replayLetter_rule_from_original
#print axioms typed_pigeonhole_of_fixedStem
#print axioms ramseySpaceOfFixedStemPigeonhole
#print axioms ellentuck_of_fixedStemPigeonhole
