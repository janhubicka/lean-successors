import SuccessorTree.V10.PrescribedRecordIndependence
import SuccessorTree.V10.LocalAgeNeutralTransport
import Mathlib.Tactic

/-!
# Recover the complete old record after insertion

Delete the inserted ordinary coordinate, retaining the distinguished
vertex and all directed L and E atoms. The same operation recovers the
source from prescribed and neutral insertions, so it also applies when
comparing images from different branches. No prefix law is assumed.
-/

namespace SuccessorTree.V10

/-- Restrict a complete record to the shifted old coordinates. -/
def PartialTypeWithE.eraseInserted
    {cut db du dd : Nat} (T : PartialTypeWithE (cut+1) db du dd)
    (ell : Nat) : PartialTypeWithE cut db du dd where
  lReduct := {
    binary := fun a b r => T.lReduct.binary
      (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b) r
    unary := fun a r => T.lReduct.unary (insertedTypeCoordinate ell a) r
    diagonal := fun a r => T.lReduct.diagonal (insertedTypeCoordinate ell a) r }
  eRelation := fun a b => T.eRelation
    (insertedTypeCoordinate ell a) (insertedTypeCoordinate ell b)

/-- Deletion on raw nodes. At or below the omitted level there is no
coordinate to delete. No admissibility of arbitrary inputs is asserted. -/
def recoverInsertedRaw {db du dd : Nat} (ell : Nat) :
    RawPartialTypeNode db du dd → RawPartialTypeNode db du dd
  | ⟨0,T⟩ => ⟨0,T⟩
  | ⟨n+1,T⟩ => if ell ≤ n then ⟨n,T.eraseInserted ell⟩ else ⟨n+1,T⟩

/-- Above the omitted level, deletion removes exactly one coordinate. -/
theorem recoverInsertedRaw_succ
    {n db du dd : Nat} (ell : Nat) (T : PartialTypeWithE (n+1) db du dd)
    (h : ell ≤ n) :
    recoverInsertedRaw ell (⟨n+1,T⟩ : RawPartialTypeNode db du dd) =
      ⟨n,T.eraseInserted ell⟩ := by
  simp only [recoverInsertedRaw, if_pos h]

/-- Every raw node below the gap is fixed by recovery. -/
theorem recoverInsertedRaw_fixed_below
    {db du dd : Nat} (ell : Nat) (a : RawPartialTypeNode db du dd)
    (h : a.1 < ell) : recoverInsertedRaw ell a = a := by
  obtain ⟨n,T⟩ := a
  cases n with
  | zero => rfl
  | succ n =>
    have hn : ¬ ell ≤ n := by change n+1 < ell at h; omega
    simp only [recoverInsertedRaw, if_neg hn]

/-- Old-record recovery for every prescribed lower column and inserted
E cut. Neither compatibility nor a forbidden-age hypothesis is needed. -/
theorem PrescribedBoringData.insertedTypeRecord_erase
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (P : LowerInsertedColumn ell db du dd) (d cut v : Nat)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hCut : cut ≤ A.size) (hv : v < A.size) :
    (F.insertedTypeRecord A P d cut v).eraseInserted ell =
      A.partialTypeAt cut v := by
  have hIn : ∀ a : Option (Fin cut), prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hCut a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change (insertL A ell (F.insertedLData A P)).binary
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a))
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell b)) r =
        A.L.binary (prefixVertexIndex v a) (prefixVertexIndex v b) r
      simp only [prefixVertexIndex_insertedTypeCoordinate, insertL_old_binary]
    · intro a r
      change (insertL A ell (F.insertedLData A P)).unary
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a)) r =
        A.L.unary (prefixVertexIndex v a) r
      simp only [prefixVertexIndex_insertedTypeCoordinate, insertL_old_unary]
    · intro a r
      change (insertL A ell (F.insertedLData A P)).diagonal
        (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a)) r =
        A.L.diagonal (prefixVertexIndex v a) r
      simp only [prefixVertexIndex_insertedTypeCoordinate, insertL_old_diagonal]
  · intro a b
    change insertE A ell d
      (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell a))
      (prefixVertexIndex (insertAddress ell v) (insertedTypeCoordinate ell b)) =
      A.E (prefixVertexIndex v a) (prefixVertexIndex v b)
    rw [prefixVertexIndex_insertedTypeCoordinate,
      prefixVertexIndex_insertedTypeCoordinate]
    exact insertE_old_pair_eq A ell d hell hPos _ _ (hIn a) (hIn b)

/-- Recovery for the literal finite prescribed constructor. -/
theorem PrescribedBoringData.prescribedInsertPartial_erase
    {ell db du dd : Nat} (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (d : Nat) (hValid : ValidNewOrdinaryColumn Q d)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hd : d ≤ ell) (hGate : d = 0 ∨ d < ell)
    (cut v : Nat) (hCut : cut ≤ A.size) (hv : v < A.size) :
    ((prescribedInsertPartial A Q d hValid hell hPos hd hGate
      (F.upperIncoming A) (F.upperOutgoing A)).partialTypeAt
        (cut+1) (insertAddress ell v)).eraseInserted ell =
      A.partialTypeAt cut v := by
  rw [F.prescribedInsertPartial_record_eq]
  exact F.insertedTypeRecord_erase A (lowerInsertedColumn Q) d cut v
    hell hPos hCut hv

/-- The same deletion recovers every complete neutral source record. -/
theorem neutralInsert_partialType_erase
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (hell : ell ≤ A.size) (hPos : 0 < ell)
    (cut v : Nat) (hCut : cut ≤ A.size) (hv : v < A.size) :
    ((neutralInsert A ell hell hPos).partialTypeAt
      (cut+1) (insertAddress ell v)).eraseInserted ell =
      A.partialTypeAt cut v := by
  have hOld := neutralInsert_partialType_old_atoms A ell hell hPos cut v hCut hv
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · exact hOld.1
    · exact hOld.2.1
    · exact hOld.2.2.1
  · exact hOld.2.2.2

end SuccessorTree.V10
