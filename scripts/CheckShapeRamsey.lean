import SuccessorTree.ShapeFiniteRamsey

/-! Run with `lake env lean scripts/CheckShapeRamsey.lean`.
The examples test the public finite-colour interface and literal composition,
not a replacement theorem with a pigeonhole hypothesis. -/

open SuccessorTree SuccessorTree.SMTree

universe u v
variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T] {S : STree T Label}

example (H : SMTree S) (n k r : Nat) (colour : AM H n k → Fin r) :
    ∃ W : ShapeSubspace H n,
      ∀ a b : AM H n k,
        colour (H.shapeActK n k W a) = colour (H.shapeActK n k W b) :=
  H.shapePreservingRamsey n k colour

example (H : SMTree S) (colour : AM H 0 0 → Fin 2) :
    ∃ W : ShapeSubspace H 0,
      ∀ a b : AM H 0 0,
        colour (H.shapeActK 0 0 W a) = colour (H.shapeActK 0 0 W b) :=
  H.shapePreservingRamsey 0 0 colour

example (H : SMTree S) (n k r : Nat) (colour : AM H n k → Fin r) :
    ∃ F : MMap H, ∃ hF : F.FixesBelow H n,
      ∀ a b : AM H n k,
        colour ((MMap.comp H F (a.representative H)).toAM H n k
          (MMap.comp_fixesBelow H F (a.representative H) n hF
            (a.representative_fixesBelow H))) =
        colour ((MMap.comp H F (b.representative H)).toAM H n k
          (MMap.comp_fixesBelow H F (b.representative H) n hF
            (b.representative_fixesBelow H))) := by
  obtain ⟨W, hW⟩ := H.shapePreservingRamsey n k colour
  exact ⟨W.1, W.2, hW⟩

#check @SuccessorTree.SMTree.shapePreservingRamsey
#check @SuccessorTree.SMTree.shapeRamsey_approximations
#print axioms SuccessorTree.SMTree.canonicalExtension_unique
#print axioms SuccessorTree.SMTree.oneDimensionalPigeonhole_shape
#print axioms SuccessorTree.SMTree.shapeOneDimensionalRamsey
#print axioms SuccessorTree.SMTree.shapeLocalPigeonhole
#print axioms SuccessorTree.SMTree.frontFusion_homogeneous
#print axioms SuccessorTree.SMTree.buildShapeProductStep
#print axioms SuccessorTree.SMTree.shapeRamsey_approximations
#print axioms SuccessorTree.SMTree.shapePreservingRamsey
