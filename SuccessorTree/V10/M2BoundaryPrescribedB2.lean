import SuccessorTree.V10.M2BoundaryTypedRecords
import Mathlib.Tactic

/-!
# Real B1/B2 boundary prescription for intrinsic M2 deletion

Index the entire source boundary level, without selecting representatives
or imposing an arbitrary extension. The input is the actual D(x)
complete L+ type at the common lower target level m, and the output is
the actual F(x) complete L+ type at m+1.

All source records are injectively indexed and satisfy B1. The existing
two-map compatibility theorem gives B2: equality of the full ordinary
L+ socle after deletion forces equality of the full ordinary L+ socle
before deletion. Thus the genuine data can be installed directly as
PrescribedBoringData. The finite L-age CompatibleB3 check is separate.
-/
namespace SuccessorTree.V10

/-- Comparing full ordinary L+ socles of two admissible Kpt nodes
at the same explicitly certified level is equivalent to comparing
their typed records. Both directions include every E and L bit. -/
theorem kptRecordAtLevel_sameOrdinary_iff
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    (n : Nat) (x y : AdmissibleKptNode family)
    (hx : LevelTree.lev x = n)
    (hy : LevelTree.lev y = n) :
    SameOrdinaryAtCut (kptRecordAtLevel n x hx)
        (kptRecordAtLevel n y hy) ↔
      ∃ h : LevelTree.lev x = LevelTree.lev y,
        SameOrdinaryAtCut x.1.2
          (cast (congrArg
            (fun k => PartialTypeWithE k db du dd) h.symm)
            y.1.2) := by
  rcases x with ⟨⟨i,R⟩,hRi⟩
  rcases y with ⟨⟨j,S⟩,hSj⟩
  change i = n at hx
  change j = n at hy
  subst i
  subst j
  constructor
  · intro h
    exact ⟨rfl,h⟩
  · rintro ⟨hEq,h⟩
    have heq : hEq = (rfl : n = n) := Subsingleton.elim _ _
    rw [heq] at h
    exact h

/-- Full compatibility transports between two arbitrary Kpt ShapeMaps
for genuine source nodes, including dependent source and target levels.
This is the node-level form of the previously checked record theorem. -/
theorem shapeMap_transfers_ordinary_compatibility_nodes
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F D : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (x y : AdmissibleKptNode family)
    (hLevels : LevelTree.lev x = LevelTree.lev y)
    (hPos : 0 < LevelTree.lev x)
    (hD :
      ∃ h : LevelTree.lev (D x) = LevelTree.lev (D y),
        SameOrdinaryAtCut (D x).1.2
          (cast (congrArg
            (fun k => PartialTypeWithE k db du dd) h.symm)
            (D y).1.2)) :
    ∃ h : LevelTree.lev (F x) = LevelTree.lev (F y),
      SameOrdinaryAtCut (F x).1.2
        (cast (congrArg
          (fun k => PartialTypeWithE k db du dd) h.symm)
          (F y).1.2) := by
  rcases x with ⟨⟨n,T⟩,hT⟩
  rcases y with ⟨⟨k,U⟩,hU⟩
  change n = k at hLevels
  subst k
  exact shapeMap_transfers_ordinary_compatibility
    family F D T U hPos hT hU hD

/-- Actual full B2 compatibility at the deleted boundary: this
is a theorem about the genuine original ShapeMap F and its
genuine first deletion factor D, not an assumed B2 property. -/
theorem m2Boundary_B2
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
    SameOrdinarySocle
      (m2Boundary_targetType family F q₀ a₀ hprev hgap x)
      (m2Boundary_targetType family F q₀ a₀ hprev hgap y) := by
  let D := uniformGapDeletedShapeMap family F q₀ a₀ hprev hgap
  let m := LevelTree.lev (F a₀)-1
  have hDComp :
      ∃ h : LevelTree.lev (D x.1) = LevelTree.lev (D y.1),
        SameOrdinaryAtCut (D x.1).1.2
          (cast (congrArg (fun k => PartialTypeWithE k db du dd) h.symm)
            (D y.1).1.2) :=
    (kptRecordAtLevel_sameOrdinary_iff m (D x.1) (D y.1)
      (m2Boundary_deleted_level family F q₀ a₀ hprev hgap x)
      (m2Boundary_deleted_level family F q₀ a₀ hprev hgap y)).1 hComp
  have hSourceLevel : LevelTree.lev x.1 = LevelTree.lev y.1 :=
    x.2.trans y.2.symm
  have hPos : 0 < LevelTree.lev x.1 := by
    have hBase : LevelTree.lev q₀ + 1 = LevelTree.lev x.1 := by
      rw [x.2]
      exact hprev
    omega
  obtain ⟨hFLevel,hFComp⟩ :=
    shapeMap_transfers_ordinary_compatibility_nodes
      family F D x.1 y.1 hSourceLevel hPos hDComp
  have hTyped := (kptRecordAtLevel_sameOrdinary_iff
    (m+1) (F x.1) (F y.1)
    (m2Boundary_target_level family F q₀ a₀ hprev hgap x)
    (m2Boundary_target_level family F q₀ a₀ hprev hgap y)).2
      ⟨hFLevel,hFComp⟩
  change SameOrdinaryAtCut
    (m2Boundary_targetType family F q₀ a₀ hprev hgap x)
    (m2Boundary_targetType family F q₀ a₀ hprev hgap y)
  exact hTyped

/-- The actual boundary partial function with B1/B2 fully
constructed, on the entire source level. Only CompatibleB3 remains
to invoke the already verified one-gap prescribed extension. -/
noncomputable def m2Boundary_prescribedData
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    PrescribedBoringData (LevelTree.lev (F a₀)-1) db du dd :=
  PrescribedBoringData.ofInjective
    (m2Boundary_sourceType family F q₀ a₀ hprev hgap)
    (m2Boundary_targetType family F q₀ a₀ hprev hgap)
    (m2Boundary_source_injective family F q₀ a₀ hprev hgap)
    (m2Boundary_B1 family F q₀ a₀ hprev hgap)
    (m2Boundary_B2 family F q₀ a₀ hprev hgap)

/-- Every true boundary image is a prescribed source, not merely a
member of a chosen finite representative family. -/
theorem m2Boundary_prescribed_source
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    m2Boundary_sourceType family F q₀ a₀ hprev hgap x ∈
      (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).source := by
  change m2Boundary_sourceType family F q₀ a₀ hprev hgap x ∈
    Set.range (m2Boundary_sourceType family F q₀ a₀ hprev hgap)
  exact ⟨x,rfl⟩

/-- Source index and prescribed target really represent F(x), with
complete L+ equality. No representative-dependent choice remains. -/
theorem m2Boundary_prescribed_target
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (x : M2BoundaryIndex family a₀) :
    (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).target
      (m2Boundary_sourceType family F q₀ a₀ hprev hgap x) =
      m2Boundary_targetType family F q₀ a₀ hprev hgap x := by
  exact PrescribedBoringData.ofInjective_target
    (m2Boundary_sourceType family F q₀ a₀ hprev hgap)
    (m2Boundary_targetType family F q₀ a₀ hprev hgap)
    (m2Boundary_source_injective family F q₀ a₀ hprev hgap)
    (m2Boundary_B1 family F q₀ a₀ hprev hgap)
    (m2Boundary_B2 family F q₀ a₀ hprev hgap) x

end SuccessorTree.V10
