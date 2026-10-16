import SuccessorTree.Library.Structures

/-!
# Transitive axiom audit for new general-purpose library exports

The full V10 and abstract shape theorem suites have their own
dedicated checkers. This small separate script guarantees that the
generic copy-Ramsey expansion theorem and intrinsic successor-event
transport, now publicly exported, rely only on standard Lean axioms.
The named log parser rejects missing, extra, duplicated or substituted
declarations, and the forbidden `sorryAx`.
-/

#print axioms SuccessorTree.RamseyExpansion.simultaneous_ramsey
#print axioms SuccessorTree.RamseyExpansion.copyRamseyDegreeLE_card_expansionTypes
#print axioms SuccessorTree.ShapeMap.mapEvent_injective
#print axioms SuccessorTree.ShapeMap.mapPointed_injective
