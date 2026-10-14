import SuccessorTree.V10.M2BoundaryLowRecords
import Mathlib.Tactic

/-!
# Reflect compatible deleted boundary records to original source types

Every actual D-boundary record is a full L+ image of one actual source
Kpt type. Since D is a genuine ShapeMap, the checked full retained
record theorem reflects ordinary-socle compatibility from two D
images back to the original source types. These genuine source
types are the exact common-socle labels required by simultaneous
nonedge padding in the multi-upper M2 B3 contradiction.
-/

namespace SuccessorTree.V10

/-- A boundary node's original fixed-level full L+ record is genuinely
admissible, with no new witness or chosen E-expansion. -/
theorem m2Boundary_original_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a₀ : AdmissibleKptNode family)
    (x : M2BoundaryIndex family a₀) :
    IsAdmissibleRawType family
      (⟨LevelTree.lev a₀,m2Boundary_originalType family a₀ x⟩ :
        RawPartialTypeNode db du dd) := by
  rw [←m2Boundary_original_raw family a₀ x]
  exact x.1.2

/-- If two actual deleted boundary inputs are ordinary-compatible
in the COMPLETE L+ record (including E and absent L bits), their
original source types are compatible. This is a genuine consequence
of D's ShapeMap fields and retained record recovery, not B2 assumed
for an abstract prescription. -/
theorem m2Boundary_original_compatible_of_deleted
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x y : M2BoundaryIndex family a₀)
    (hComp : SameOrdinaryAtCut
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap x)
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap y)) :
    SameOrdinaryAtCut
      (m2Boundary_originalType family a₀ x)
      (m2Boundary_originalType family a₀ y) := by
  let n := LevelTree.lev a₀
  let m := LevelTree.lev (F a₀)-1
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  let Tx := m2Boundary_originalType family a₀ x
  let Ty := m2Boundary_originalType family a₀ y
  have hx : IsAdmissibleRawType family
      (⟨n,Tx⟩ : RawPartialTypeNode db du dd) :=
    m2Boundary_original_admissible family a₀ x
  have hy : IsAdmissibleRawType family
      (⟨n,Ty⟩ : RawPartialTypeNode db du dd) :=
    m2Boundary_original_admissible family a₀ y
  let ux : AdmissibleKptNode family := ⟨⟨n,Tx⟩,hx⟩
  let uy : AdmissibleKptNode family := ⟨⟨n,Ty⟩,hy⟩
  have hux : ux = x.1 :=
    Subtype.ext (m2Boundary_original_raw family a₀ x).symm
  have huy : uy = y.1 :=
    Subtype.ext (m2Boundary_original_raw family a₀ y).symm
  have hDeleted :
      ∃ h : LevelTree.lev (D x.1) = LevelTree.lev (D y.1),
        SameOrdinaryAtCut (D x.1).1.2
          (cast (congrArg (fun k => PartialTypeWithE k db du dd) h.symm)
            (D y.1).1.2) :=
    (kptRecordAtLevel_sameOrdinary_iff m (D x.1) (D y.1)
      (m2Boundary_deleted_level family F q₀ a₀ hprev hgap x)
      (m2Boundary_deleted_level family F q₀ a₀ hprev hgap y)).1 hComp
  have hMapped :
      ∃ h : LevelTree.lev (D ux) = LevelTree.lev (D uy),
        SameOrdinaryAtCut (D ux).1.2
          (cast (congrArg (fun k => PartialTypeWithE k db du dd) h.symm)
            (D uy).1.2) := by
    simpa only [hux,huy] using hDeleted
  exact shapeMap_reflects_source_compatibility family D Tx Ty hx hy hMapped

/-- Transport a selected upper L-type through the exact dependent
boundary image index. This includes the omitted target coordinate
m, not just the retained old levels. -/
theorem m2Boundary_upper_L_type_of_source_index
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀)
    (W : AgeTestModel db du dd) (w : Nat)
    (hType : RelationalPrefixType.ofAgeModel W
      ((LevelTree.lev (F a₀)-1)+1) w =
        (m2Boundary_targetType family F q₀ a₀ hprev hgap x).lReduct) :
    RelationalPrefixType.ofAgeModel W (LevelTree.lev (F x.1)) w =
      (F x.1).1.2.lReduct := by
  rw [m2Boundary_target_raw family F q₀ a₀ hprev hgap x]
  exact hType

end SuccessorTree.V10
