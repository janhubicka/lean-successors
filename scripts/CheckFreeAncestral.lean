import SuccessorTree.FreeAncestralFiniteRamsey

/-!
Focused axiom audit for the concrete free ancestral history tree.
Run after `lake build` via `lake env lean scripts/CheckFreeAncestral.lean`.
-/

#check @SuccessorTree.FreeAncestral.freeSTree
#check @SuccessorTree.FreeAncestral.freeSMTree
#check @SuccessorTree.FreeAncestral.finiteShapeRamsey

#print axioms SuccessorTree.FreeAncestral.free_m2_exists
#print axioms SuccessorTree.FreeAncestral.free_m3_exists
#print axioms SuccessorTree.FreeAncestral.freeSMTree
#print axioms SuccessorTree.FreeAncestral.finiteShapeRamsey
#print axioms SuccessorTree.ShapeMap.mapEvent_injective
#print axioms SuccessorTree.ShapeMap.mapPointed_injective
#print axioms SuccessorTree.ShapeMap.mapPointed_ne_of_address_ne
