import SuccessorTree.FatTree.A4Trace

open SuccessorTree

#check SMTree.FiniteFatTree.appendRow
#check SMTree.FiniteFatTree.appendRow_height
#check SMTree.FiniteFatTree.appendRow_cut_old
#check SMTree.FiniteFatTree.appendRow_terminalCut
#check SMTree.FiniteFatTree.appendRow_row_old
#check SMTree.FiniteFatTree.appendRow_row_last
#check SMTree.FiniteFatTree.appendRow_initialSegment

#print axioms SMTree.FiniteFatTree.appendRow_initialSegment

#check SMTree.FiniteFatTree.traceLift_appendRow
#check SMTree.FiniteFatTree.traceLift_appendRow_fan
#print axioms SMTree.FiniteFatTree.traceLift_appendRow
#print axioms SMTree.FiniteFatTree.traceLift_appendRow_fan

#check SMTree.FiniteFatTree.IsExactTrace
#check SMTree.FiniteFatTree.ExactTrace
#check SMTree.FiniteFatTree.exactTraces_finite
#print axioms SMTree.FiniteFatTree.exactTraces_finite

#check SMTree.FiniteFatTree.ExactTrace.appendRow_image_mem_fan
#print axioms SMTree.FiniteFatTree.ExactTrace.appendRow_image_mem_fan

#check SMTree.FiniteFatTree.IsRawTraceUpdate
#check SMTree.FiniteFatTree.ExactTrace.extendByLetter
#print axioms SMTree.FiniteFatTree.ExactTrace.extendByLetter
#check SMTree.FiniteFatTree.ExactTrace.exists_raw_predecessor
#print axioms SMTree.FiniteFatTree.ExactTrace.exists_raw_predecessor
#check SMTree.FiniteFatTree.isExactTrace_appendRow_iff
#print axioms SMTree.FiniteFatTree.isExactTrace_appendRow_iff
