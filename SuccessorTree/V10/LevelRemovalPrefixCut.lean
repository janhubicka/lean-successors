import SuccessorTree.V10.LevelRemovalWitnessCut
import SuccessorTree.V10.AdmissibleKptLevelTree
import Mathlib.Tactic

/-!
# A predecessor's certified free cut persists into every upper witness

The complete L+ prefix relation is equality of the entire induced
initial-socle record, not just its ordinary L reduct. Consequently a
certified E free cut of the last ordinary vertex of one complete
prefix is also the ACTUAL free cut of that coordinate in every finite
enumerated partial structure representing a later complete type.

This is the witness-independent bridge required after the genuine
mapped successor from LevelRemovalGapColumn: the weak image
successor is only below F(b), but its last-ordinary-column guard
persists in the complete type of F(b). No uniform deletion, M2 or
corrected-B3 necessity is asserted here.
-/

namespace SuccessorTree.V10

/-- A complete level-(ell+1) L+ record with a valid E-column,
embedded as an ACTUAL complete raw prefix of a represented type,
determines the ambient free cut of vertex ell.

The ambient representative may have additional ordinary vertices,
and no arbitrary extra E structure is demanded of an L-age witness. -/
theorem validNewColumn_rawPrefix_ambient_freeCut_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hPrefix :
      (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd) ≤
        A.rawTypeAtFree v)
    (f : Nat) (hf : f ≤ ell)
    (hValid : ValidNewOrdinaryColumn Q f) :
    A.freeLevel ell = f := by
  have hBound : ell + 1 ≤ A.freeLevel v := hPrefix.1
  have hQ :
      Q = (A.partialTypeAt (A.freeLevel v) v).restrict hBound :=
    hPrefix.2
  have hType : Q = A.partialTypeAt (ell + 1) v := by
    calc
      Q = (A.partialTypeAt (A.freeLevel v) v).restrict hBound := hQ
      _ = A.partialTypeAt (ell + 1) v :=
        A.partialTypeAt_restrict (ell + 1) (A.freeLevel v) v hBound
  exact validNewColumn_ambient_freeCut_eq
    A v ell hv hBound Q hType f hf hValid

/-- If a genuine admissible Kpt successor is below a longer Kpt
type, its valid new-ordinary E column has the same free cut in
every finite representative of that longer type. -/
theorem validNewColumn_below_Kpt_witness_freeCut_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (d b : AdmissibleKptNode family)
    (ell : Nat) (Q : PartialTypeWithE (ell + 1) db du dd)
    (hRaw : d.1 =
      (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd))
    (hdb : d ≤ b)
    (f : Nat) (hf : f ≤ ell)
    (hValid : ValidNewOrdinaryColumn Q f)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRep : b.1 = A.rawTypeAtFree v) :
    A.freeLevel ell = f := by
  have hPrefix :
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) ≤
        A.rawTypeAtFree v := by
    calc
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) = d.1 := hRaw.symm
      _ ≤ b.1 := hdb
      _ = A.rawTypeAtFree v := hRep
  exact validNewColumn_rawPrefix_ambient_freeCut_eq
    A v ell hv Q hPrefix f hf hValid

/-- The strict guard needed at the next ordinary column for deletion
is inherited by ANY finite representative of an upper type: the
choice of source successor and of finite witness are separate issues. -/
theorem guarded_gap_column_below_Kpt_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (d b : AdmissibleKptNode family)
    (ell m : Nat)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hRaw : d.1 =
      (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd))
    (hdb : d ≤ b)
    (f : Nat) (hf : f ≤ ell)
    (hValid : ValidNewOrdinaryColumn Q f)
    (hLow : f < m)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRep : b.1 = A.rawTypeAtFree v) :
    A.freeLevel ell < m := by
  have hh := validNewColumn_below_Kpt_witness_freeCut_eq
    family d b ell Q hRaw hdb f hf hValid A v hv hRep
  omega

end SuccessorTree.V10
