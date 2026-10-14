import SuccessorTree.V10.PrescribedIncidentIndependence
import SuccessorTree.V10.LocalAgeNeutralIndependence
import Mathlib.Tactic

/-!
# Complete prescribed insertion records are independent of their witnesses

Combine exact old-atom transport with the record-determined gated incident
columns. This proves equality of every L+ atom of the inserted type for two
ambient realizations of the same source type. It includes the distinguished
vertex, directed nonrelations, loops, unary/diagonal data and all E pairs.

The raw record is identified with extraction from the actual finite
prescribedInsertPartial constructor. Ordinary-socle compatibility identifies
both the lower L-column and the inserted E-cut, so the final theorem also
allows different compatible prescribed-output representatives.

This does not yet construct the total admissible Kpt map or prove its weak
successor law. Those are separate from this finite well-definedness theorem.
-/

namespace SuccessorTree.V10

/-- Literal full L+ record of the prescribed finite insertion, without
bundling the proof that the ambient insertion satisfies the partial axioms. -/
noncomputable def PrescribedBoringData.insertedTypeRecord
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd)
    (d cut v : Nat) : PartialTypeWithE (cut + 1) db du dd where
  lReduct := RelationalPrefixType.ofAgeModel
    (insertL A ell (F.insertedLData A P)) (cut + 1) (insertAddress ell v)
  eRelation := fun a b => insertE A ell d
    (prefixVertexIndex (insertAddress ell v) a)
    (prefixVertexIndex (insertAddress ell v) b)

/-- Equality of source records determines the ENTIRE inserted record,
not just its restriction to old coordinates or its L-reduct. -/
theorem PrescribedBoringData.insertedTypeRecord_independent
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A C : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd)
    (d cut v w : Nat)
    (hPos : 0 < ell) (hEll : ell ≤ cut) (hd : d ≤ ell)
    (hcutA : cut ≤ A.size) (hcutC : cut ≤ C.size)
    (hvCut : cut ≤ v) (hwCut : cut ≤ w)
    (hv : v < A.size) (hw : w < C.size)
    (hFull : A.partialTypeAt cut v = C.partialTypeAt cut w) :
    F.insertedTypeRecord A P d cut v =
      F.insertedTypeRecord C P d cut w := by
  have hellA : ell ≤ A.size := hEll.trans hcutA
  have hellC : ell ≤ C.size := hEll.trans hcutC
  have hSkip : ∀ x, insertAddress ell x ≠ ell := by
    intro x
    unfold insertAddress
    split_ifs <;> omega
  have hInA : ∀ a : Option (Fin cut), prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hcutA a
  have hInC : ∀ a : Option (Fin cut), prefixVertexIndex w a < C.size :=
    fun a => prefixVertexIndex_inside w C.size hw hcutC a
  have hInc := F.insertedLData_coordinate_eq A C P cut v w
    hEll hvCut hwCut hFull
  have hSmall : ∀ a : Option (Fin cut),
      (prefixVertexIndex v a < d ↔ prefixVertexIndex w a < d) := by
    intro a
    cases a with
    | none => change v < d ↔ w < d; omega
    | some a => rfl
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      rcases insertedTypeCoordinate_cases cut ell hEll a with
        ha | ⟨a0, ha⟩
      · subst a
        rcases insertedTypeCoordinate_cases cut ell hEll b with
          hb | ⟨b0, hb⟩
        · subst b
          change (insertL A ell (F.insertedLData A P)).binary ell ell r =
            (insertL C ell (F.insertedLData C P)).binary ell ell r
          simp [insertL, PrescribedBoringData.insertedLData, gatedInsertedLData]
        · subst b
          change (insertL A ell (F.insertedLData A P)).binary ell
              (prefixVertexIndex (insertAddress ell v)
                (insertedTypeCoordinate ell b0)) r =
            (insertL C ell (F.insertedLData C P)).binary ell
              (prefixVertexIndex (insertAddress ell w)
                (insertedTypeCoordinate ell b0)) r
          rw [prefixVertexIndex_insertedTypeCoordinate,
            prefixVertexIndex_insertedTypeCoordinate]
          simpa [insertL, hSkip] using (hInc b0 r).2
      · subst a
        rcases insertedTypeCoordinate_cases cut ell hEll b with
          hb | ⟨b0, hb⟩
        · subst b
          change (insertL A ell (F.insertedLData A P)).binary
              (prefixVertexIndex (insertAddress ell v)
                (insertedTypeCoordinate ell a0)) ell r =
            (insertL C ell (F.insertedLData C P)).binary
              (prefixVertexIndex (insertAddress ell w)
                (insertedTypeCoordinate ell a0)) ell r
          rw [prefixVertexIndex_insertedTypeCoordinate,
            prefixVertexIndex_insertedTypeCoordinate]
          simpa [insertL, hSkip] using (hInc a0 r).1
        · subst b
          change (insertL A ell (F.insertedLData A P)).binary
              (prefixVertexIndex (insertAddress ell v)
                (insertedTypeCoordinate ell a0))
              (prefixVertexIndex (insertAddress ell v)
                (insertedTypeCoordinate ell b0)) r =
            (insertL C ell (F.insertedLData C P)).binary
              (prefixVertexIndex (insertAddress ell w)
                (insertedTypeCoordinate ell a0))
              (prefixVertexIndex (insertAddress ell w)
                (insertedTypeCoordinate ell b0)) r
          simp only [prefixVertexIndex_insertedTypeCoordinate, insertL_old_binary]
          exact congrArg (fun T : PartialTypeWithE cut db du dd =>
            T.lReduct.binary a0 b0 r) hFull
    · intro a r
      rcases insertedTypeCoordinate_cases cut ell hEll a with
        ha | ⟨a0, ha⟩
      · subst a
        change (insertL A ell (F.insertedLData A P)).unary ell r =
          (insertL C ell (F.insertedLData C P)).unary ell r
        simp [insertL, PrescribedBoringData.insertedLData, gatedInsertedLData]
      · subst a
        change (insertL A ell (F.insertedLData A P)).unary
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell a0)) r =
          (insertL C ell (F.insertedLData C P)).unary
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell a0)) r
        simp only [prefixVertexIndex_insertedTypeCoordinate, insertL_old_unary]
        exact congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.lReduct.unary a0 r) hFull
    · intro a r
      rcases insertedTypeCoordinate_cases cut ell hEll a with
        ha | ⟨a0, ha⟩
      · subst a
        change (insertL A ell (F.insertedLData A P)).diagonal ell r =
          (insertL C ell (F.insertedLData C P)).diagonal ell r
        simp [insertL, PrescribedBoringData.insertedLData, gatedInsertedLData]
      · subst a
        change (insertL A ell (F.insertedLData A P)).diagonal
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell a0)) r =
          (insertL C ell (F.insertedLData C P)).diagonal
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell a0)) r
        simp only [prefixVertexIndex_insertedTypeCoordinate, insertL_old_diagonal]
        exact congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.lReduct.diagonal a0 r) hFull
  · intro a b
    rcases insertedTypeCoordinate_cases cut ell hEll a with
      ha | ⟨a0, ha⟩
    · subst a
      rcases insertedTypeCoordinate_cases cut ell hEll b with
        hb | ⟨b0, hb⟩
      · subst b
        change insertE A ell d ell ell = insertE C ell d ell ell
        rw [insertE_new_loop_false A ell d hd,
          insertE_new_loop_false C ell d hd]
      · subst b
        change insertE A ell d ell
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell b0)) =
          insertE C ell d ell
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell b0))
        rw [prefixVertexIndex_insertedTypeCoordinate,
          prefixVertexIndex_insertedTypeCoordinate,
          insertE_new_row_eq A ell d hellA _ (hInA b0),
          insertE_new_row_eq C ell d hellC _ (hInC b0)]
        have hGate := freeLevel_gate_iff_of_partialType_eq A C ell
          (prefixVertexIndex v b0) (prefixVertexIndex w b0)
          (partialTypeAt_coordinate_eq_of_fullType_eq
            A C ell cut v w hEll hFull b0)
        simp only [hGate]
    · subst a
      rcases insertedTypeCoordinate_cases cut ell hEll b with
        hb | ⟨b0, hb⟩
      · subst b
        change insertE A ell d
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell a0)) ell =
          insertE C ell d
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell a0)) ell
        rw [prefixVertexIndex_insertedTypeCoordinate,
          prefixVertexIndex_insertedTypeCoordinate,
          insertE_new_column_eq A ell d hellA hd,
          insertE_new_column_eq C ell d hellC hd]
        simp only [hSmall a0]
      · subst b
        change insertE A ell d
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell a0))
            (prefixVertexIndex (insertAddress ell v)
              (insertedTypeCoordinate ell b0)) =
          insertE C ell d
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell a0))
            (prefixVertexIndex (insertAddress ell w)
              (insertedTypeCoordinate ell b0))
        simp only [prefixVertexIndex_insertedTypeCoordinate]
        rw [insertE_old_pair_eq A ell d hellA hPos _ _ (hInA a0) (hInA b0),
          insertE_old_pair_eq C ell d hellC hPos _ _ (hInC a0) (hInC b0)]
        exact congrArg (fun T : PartialTypeWithE cut db du dd =>
          T.eRelation a0 b0) hFull

/-- The record above is exactly the type extracted from the genuine
finite prescribed L+ insertion, not a separate surrogate construction. -/
theorem PrescribedBoringData.prescribedInsertPartial_record_eq
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hd : d ≤ ell) (hdGate : d = 0 ∨ d < ell)
    (cut v : Nat) :
    (prescribedInsertPartial A Q d hValid hell hPos hd hdGate
      (F.upperIncoming A) (F.upperOutgoing A)).partialTypeAt
        (cut + 1) (insertAddress ell v) =
      F.insertedTypeRecord A (lowerInsertedColumn Q) d cut v := by
  rfl

/-- Both the ambient realization and the compatible prescribed-output
representative can vary. B2 supplies hSocle; the canonical E-cut equality
is DERIVED rather than imposed as an additional hypothesis. -/
theorem PrescribedBoringData.prescribedInsertPartial_independent
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A C : EnumeratedPartialStructure db du dd)
    (Q R : PartialTypeWithE (ell + 1) db du dd)
    (d e : Nat)
    (hQ : ValidNewOrdinaryColumn Q d) (hR : ValidNewOrdinaryColumn R e)
    (hSocle : SameOrdinarySocle Q R)
    (hd : d ≤ ell) (he : e ≤ ell)
    (hdGate : d = 0 ∨ d < ell) (heGate : e = 0 ∨ e < ell)
    (cut v w : Nat)
    (hPos : 0 < ell) (hEll : ell ≤ cut)
    (hcutA : cut ≤ A.size) (hcutC : cut ≤ C.size)
    (hvCut : cut ≤ v) (hwCut : cut ≤ w)
    (hv : v < A.size) (hw : w < C.size)
    (hFull : A.partialTypeAt cut v = C.partialTypeAt cut w) :
    (prescribedInsertPartial A Q d hQ (hEll.trans hcutA) hPos hd hdGate
      (F.upperIncoming A) (F.upperOutgoing A)).partialTypeAt
        (cut + 1) (insertAddress ell v) =
      (prescribedInsertPartial C R e hR (hEll.trans hcutC) hPos he heGate
        (F.upperIncoming C) (F.upperOutgoing C)).partialTypeAt
          (cut + 1) (insertAddress ell w) := by
  have hCut := lowerInsertedCut_eq_of_sameSocle hSocle d e hd he hQ hR
  have hColumn := lowerInsertedColumn_eq_of_sameSocle hSocle
  rw [F.prescribedInsertPartial_record_eq,
    F.prescribedInsertPartial_record_eq, ← hCut, ← hColumn]
  exact F.insertedTypeRecord_independent A C (lowerInsertedColumn Q)
    d cut v w hPos hEll hd hcutA hcutC hvCut hwCut hv hw hFull

end SuccessorTree.V10
