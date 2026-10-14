import SuccessorTree.V10.ExtractedSuccessorS2
import SuccessorTree.V10.EmptyParameterS2
import SuccessorTree.V10.AdmissibleKptMeet
import Mathlib.Tactic

/-!
# The canonical gap column has the same free cut in every actual witness

The complete E bits of an admissible Kpt successor determine the
free level of its last ordinary vertex in ANY enumerated partial
structure realizing that successor. One cannot change the
free cut by choosing a different finite representative.

This converts a record-level ValidNewOrdinaryColumn certificate
into the literal strict guard fl_A(m+1)<m required by the local
vertex-deletion construction, whenever the certificate says f<m.
The boundary successor which supplies that certificate is handled
separately by LevelRemovalGapColumn.

No new age hypothesis, global ShapeMap deletion, or M2 axiom is used.
-/

namespace SuccessorTree.V10

/-- A valid E/free-cut column on a complete extracted L+ type
has exactly the same cut as the actual corresponding ordinary
vertex of its ambient enumerated partial structure. -/
theorem validNewColumn_ambient_freeCut_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat)
    (hv : v < A.size)
    (hFull : ell + 1 ≤ A.freeLevel v)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hType : Q = A.partialTypeAt (ell + 1) v)
    (f : Nat) (hf : f ≤ ell)
    (hValid : ValidNewOrdinaryColumn Q f) :
    A.freeLevel ell = f := by
  have hActual : ValidNewOrdinaryColumn
      (A.partialTypeAt (ell + 1) v) (A.freeLevel ell) :=
    validNewColumn_of_extracted_partialType A v ell hv hFull
  have hValidA : ValidNewOrdinaryColumn
      (A.partialTypeAt (ell + 1) v) f := by
    rw [←hType]
    exact hValid
  have hUnique :=
    validNewColumn_freeCut_unique
      (A.partialTypeAt (ell + 1) v)
      f (A.freeLevel ell) hf (A.freeLevel_le ell)
      hValidA hActual
  exact hUnique.symm

/-- The canonical new-ordinary free cut encoded in any admissible
level-(ell+1) complete Kpt record is independent of its choice
of finite forbidden-free representative, including E data. -/
theorem validNewColumn_any_Kpt_witness_freeCut_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (b : AdmissibleKptNode family)
    (ell : Nat)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hRaw : b.1 =
      (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd))
    (f : Nat) (hf : f ≤ ell)
    (hValid : ValidNewOrdinaryColumn Q f)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRep : b.1 = A.rawTypeAtFree v) :
    A.freeLevel ell = f := by
  have hBoth :
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
        A.rawTypeAtFree v := hRaw.symm.trans hRep
  have hCut : A.freeLevel v = ell + 1 := by
    have hh := congrArg Sigma.fst hBoth
    change ell + 1 = A.freeLevel v at hh
    exact hh.symm
  have hComplete :
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
        (⟨ell+1,A.partialTypeAt (ell+1) v⟩ :
          RawPartialTypeNode db du dd) := by
    calc
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
          A.rawTypeAtFree v := hBoth
      _ = (⟨ell+1,A.partialTypeAt (ell+1) v⟩ :
          RawPartialTypeNode db du dd) := by
        change
          (⟨A.freeLevel v,
            A.partialTypeAt (A.freeLevel v) v⟩ :
            RawPartialTypeNode db du dd) = _
        rw [hCut]
  have hType : Q = A.partialTypeAt (ell+1) v := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      using hComplete
  exact validNewColumn_ambient_freeCut_eq
    A v ell hv (by omega) Q hType f hf hValid

/-- In particular, the strict deletion guard on a genuine finite
representative is the same strict bound established on the
canonical successor's complete L+ column. -/
theorem guarded_column_any_Kpt_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (b : AdmissibleKptNode family)
    (ell m : Nat)
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hRaw : b.1 =
      (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd))
    (f : Nat) (hf : f ≤ ell)
    (hValid : ValidNewOrdinaryColumn Q f)
    (hBelow : f < m)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRep : b.1 = A.rawTypeAtFree v) :
    A.freeLevel ell < m := by
  rw [validNewColumn_any_Kpt_witness_freeCut_eq
    family b ell Q hRaw f hf hValid A v hv hRep]
  exact hBelow

end SuccessorTree.V10
