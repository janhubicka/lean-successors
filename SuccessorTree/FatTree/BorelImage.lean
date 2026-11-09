import SuccessorTree.FatTree.A4ReviewComplete
import SuccessorTree.FatTree.ShapeCorrespondence
import RamseySpace.FiniteColouring

/-!
# Borel colourings on images of fat subtrees

This module isolates two ingredients of the corrected manuscript:

* the map carried by a fat tree is determined on the first n+1 source
  levels by its first n+1 rows;
* a finite colouring of carried shape maps is homogeneous on a fixed-stem
  fat neighbourhood when the pullback colour fibres have the fat Ellentuck
  Baire property.

The implication from a pointwise-Borel colouring to this Baire-fibre
hypothesis requires the product-topology continuity adapter. It is not
assumed or claimed here. No algebraic cone or EA hypothesis is used.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- The values at source levels at most n are computed by the first
n+1 row extensions of the fat tree. -/
theorem associatedMap_eq_stage_of_level_le
    (U : FatTree H) (n : Nat) (x : T)
    (hx : LevelTree.lev x ≤ n) :
    associatedMap H U x = partialMap H U (n + 1) x := by
  rw [associatedMap_apply H U x]
  exact (ShapeMap.fusion_stable_of_le
    (fun i => (partialMap H U (i + 1)).map)
    (partialMap_fusionStable H U) x hx).symm

/-- The fixed-stem finite-colour fat-image theorem given Baire pullback
fibres. This uses only the unconditional fat-tree Ellentuck theorem. -/
theorem fatImageHomogeneous_of_BaireFibres
    {κ : Type w} [Fintype κ]
    {n : Nat} (a : (approximationSystem H).Approx n)
    (A : FatTree H)
    (hne : ((approximationSystem H).neighborhood a A).Nonempty)
    (colour : MMap H → κ)
    (hBaire : ∀ c : κ,
      @BaireMeasurableSet (FatTree H)
        (approximationSystem H).ellentuckTopology
        {U | colour (associatedMap H U) = c}) :
    ∃ B, B ∈ (approximationSystem H).neighborhood a A ∧
      ∃ c : κ, ∀ U,
        U ∈ (approximationSystem H).neighborhood a B →
          colour (associatedMap H U) = c := by
  exact RamseySpace.finiteBaireColouring
    (fatTreeEllentuck H) a A hne
    (fun U => colour (associatedMap H U)) hBaire

end SuccessorTree.SMTree.FatTree
