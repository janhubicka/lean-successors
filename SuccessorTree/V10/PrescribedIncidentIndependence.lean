import SuccessorTree.V10.PrescribedSourceRecovery
import Mathlib.Tactic

/-!
# Prescribed incident columns depend only on the complete source record

The apparent ambient dependence in the upper L-column is its E gate
`ell <= A.freeLevel u`. For a positive insertion level this is exactly
`E(ell-1,u)`, already present in the source type through ell. Thus both
positive and absent incident L-atoms are independent of the ambient
realization, including at its distinguished type vertex.

Together with B2's lower-column choice independence, these are the inputs
for equality of the entire inserted record. No global ShapeMap or M2/M3
conclusion is asserted in this module.
-/

namespace SuccessorTree.V10

/-- The gate at ell is recovered from the complete type through ell.
At ell=0 both gates are true; no nonexistent coordinate ell-1 is used. -/
theorem freeLevel_gate_iff_of_partialType_eq
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell u v : Nat)
    (hType : A.partialTypeAt ell u = C.partialTypeAt ell v) :
    ell ≤ A.freeLevel u ↔ ell ≤ C.freeLevel v := by
  by_cases hZero : ell = 0
  · subst ell
    simp
  · have hPos : 0 < ell := by omega
    let i : Fin ell := ⟨ell - 1, by omega⟩
    have hE := congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.eRelation (some i) none) hType
    change A.E (ell - 1) u = C.E (ell - 1) v at hE
    constructor
    · intro h
      have ha : A.E (ell - 1) u = true :=
        (A.E_iff_freeLevel (ell - 1) u).2 (by omega)
      have hc := (C.E_iff_freeLevel (ell - 1) v).1
        (hE.symm.trans ha)
      omega
    · intro h
      have hc : C.E (ell - 1) v = true :=
        (C.E_iff_freeLevel (ell - 1) v).2 (by omega)
      have ha := (A.E_iff_freeLevel (ell - 1) u).1
        (hE.trans hc)
      omega

/-- One complete longer record determines the shorter source type at
EVERY coordinate, ordinary or distinguished. The two distinguished
vertices need not have the same ambient enumeration index. -/
theorem partialTypeAt_coordinate_eq_of_fullType_eq
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell cut v w : Nat) (hEll : ell ≤ cut)
    (hFull : A.partialTypeAt cut v = C.partialTypeAt cut w)
    (a : Option (Fin cut)) :
    A.partialTypeAt ell (prefixVertexIndex v a) =
      C.partialTypeAt ell (prefixVertexIndex w a) := by
  cases a with
  | none =>
    change A.partialTypeAt ell v = C.partialTypeAt ell w
    calc
      A.partialTypeAt ell v =
          (A.partialTypeAt cut v).restrict hEll :=
        (A.partialTypeAt_restrict ell cut v hEll).symm
      _ = (C.partialTypeAt cut w).restrict hEll :=
        congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.restrict hEll) hFull
      _ = C.partialTypeAt ell w :=
        C.partialTypeAt_restrict ell cut w hEll
  | some a =>
    exact partialTypeAt_ordinary_eq_of_fullType_eq
      A C ell cut a.val v w hEll a.isLt hFull

/-- Existence of a matching prescribed input depends only on the ordinary
socle, not on the distinguished vertex of the queried source record. -/
theorem PrescribedBoringData.hasCompatibleSource_iff_of_sameOrdinary
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    {T U : PartialTypeWithE ell db du dd}
    (hTU : SameOrdinaryAtCut T U) :
    F.HasCompatibleSource T ↔ F.HasCompatibleSource U := by
  constructor
  · rintro ⟨S, hS, hST⟩
    exact ⟨S, hS, sameOrdinaryAtCut_trans hST hTU⟩
  · rintro ⟨S, hS, hSU⟩
    exact ⟨S, hS, sameOrdinaryAtCut_trans hSU
      (sameOrdinaryAtCut_symm hTU)⟩

/-- The chosen lower column, including the none/neutral alternative,
is constant on each ordinary-socle compatibility class. -/
theorem PrescribedBoringData.selectedLowerColumn_eq_of_sameOrdinary
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    {T U : PartialTypeWithE ell db du dd}
    (hTU : SameOrdinaryAtCut T U) :
    F.selectedLowerColumn T = F.selectedLowerColumn U := by
  classical
  by_cases hT : F.HasCompatibleSource T
  · obtain ⟨S, hS, hST⟩ := hT
    exact (F.selectedLowerColumn_eq T S hS hST).trans
      (F.selectedLowerColumn_eq U S hS
        (sameOrdinaryAtCut_trans hST hTU)).symm
  · have hU : ¬ F.HasCompatibleSource U := by
      intro h
      exact hT ((F.hasCompatibleSource_iff_of_sameOrdinary hTU).2 h)
    rw [F.selectedLowerColumn_none T hT,
      F.selectedLowerColumn_none U hU]

/-- Both directed upper tables are recovered from the shorter full source
record; no value of f outside its domain is used. -/
theorem PrescribedBoringData.upper_bits_eq_of_partialType_eq
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A C : EnumeratedPartialStructure db du dd)
    (u v : Nat)
    (hType : A.partialTypeAt ell u = C.partialTypeAt ell v)
    (r : Fin db) :
    F.upperIncoming A u r = F.upperIncoming C v r ∧
      F.upperOutgoing A u r = F.upperOutgoing C v r := by
  constructor <;>
    simp only [PrescribedBoringData.upperIncoming,
      PrescribedBoringData.upperOutgoing, hType]

/-- The ENTIRE gated incident column at every source coordinate is
independent of the ambient witness. The common lower column is explicit;
B2 gives its choice independence. Ordinary upper coordinates and the
possibly differently indexed distinguished vertices are both covered. -/
theorem PrescribedBoringData.insertedLData_coordinate_eq
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A C : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd)
    (cut v w : Nat) (hEll : ell ≤ cut)
    (hv : cut ≤ v) (hw : cut ≤ w)
    (hFull : A.partialTypeAt cut v = C.partialTypeAt cut w)
    (a : Option (Fin cut)) (r : Fin db) :
    (F.insertedLData A P).incoming (prefixVertexIndex v a) r =
        (F.insertedLData C P).incoming (prefixVertexIndex w a) r ∧
      (F.insertedLData A P).outgoing (prefixVertexIndex v a) r =
        (F.insertedLData C P).outgoing (prefixVertexIndex w a) r := by
  have hSource := partialTypeAt_coordinate_eq_of_fullType_eq
    A C ell cut v w hEll hFull a
  cases a with
  | none =>
    change A.partialTypeAt ell v = C.partialTypeAt ell w at hSource
    have hGate := freeLevel_gate_iff_of_partialType_eq
      A C ell v w hSource
    have hnv : ¬ v < ell := by omega
    have hnw : ¬ w < ell := by omega
    constructor <;>
      simp [prefixVertexIndex, PrescribedBoringData.insertedLData,
        gatedInsertedLData, hnv, hnw, hGate,
        PrescribedBoringData.upperIncoming,
        PrescribedBoringData.upperOutgoing, hSource]
  | some a =>
    change A.partialTypeAt ell a.val = C.partialTypeAt ell a.val at hSource
    have hGate := freeLevel_gate_iff_of_partialType_eq
      A C ell a.val a.val hSource
    constructor <;>
      simp [prefixVertexIndex, PrescribedBoringData.insertedLData,
        gatedInsertedLData, hGate,
        PrescribedBoringData.upperIncoming,
        PrescribedBoringData.upperOutgoing, hSource]

end SuccessorTree.V10
