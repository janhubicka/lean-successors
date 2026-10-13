import SuccessorTree.V10.CanonicalStepRealization
import Mathlib.Tactic

/-!
# Canonical successor at every prefix below a genuine free cut

The existing canonical-step realization takes a witness vertex whose
free cut is exactly ell+1. For the M2 padded source witness we instead
have ONE terminal witness of a large type, and need its actual
successor decomposition at each shorter coordinate ell.

Prefix closure supplies the admissible shorter target. The parameter
is the same genuine free-cut type of ordinary vertex ell in the one
ambient structure, never an abstract freely chosen realization.
-/

namespace SuccessorTree.V10

/-- A canonical successor for each initial prefix of a genuine
ambient type, retaining its concrete nonempty parameter. -/
theorem exists_canonical_step_from_ambient_prefix
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hCut : ell + 1 ≤ A.freeLevel v) :
    ∃ (a b : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : RawKptLetter db du dd),
      IsCanonicalKptStep family a p c b ∧
      a ⋖ b ∧
      b.1 = (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
        RawPartialTypeNode db du dd) ∧
      (0 < A.freeLevel ell →
        ∃ q : AdmissibleKptNode family,
          q ∈ p ∧ q.1 = A.rawTypeAtFree ell) := by
  let Q : PartialTypeWithE (ell + 1) db du dd :=
    A.partialTypeAt (ell + 1) v
  have hRoot : IsAdmissibleRawType family (A.rawTypeAtFree v) :=
    ⟨A, v, hv, hAvoid, rfl⟩
  have hAdB : IsAdmissibleRawType family
      (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) := by
    have hPrefix :=
      admissibleRawType_closed_under_prefix family hRoot (ell + 1) hCut
    change IsAdmissibleRawType family
      (⟨ell + 1, (A.partialTypeAt (A.freeLevel v) v).restrict hCut⟩ :
        RawPartialTypeNode db du dd) at hPrefix
    rw [A.partialTypeAt_restrict (ell + 1) (A.freeLevel v) v hCut] at hPrefix
    exact hPrefix
  let b : AdmissibleKptNode family :=
    ⟨⟨ell + 1, Q⟩, hAdB⟩
  have hAdA : IsAdmissibleRawType family
      (⟨ell, Q.restrict (Nat.le_succ ell)⟩ :
        RawPartialTypeNode db du dd) :=
    admissibleRawType_of_prefix family hAdB
      ⟨Nat.le_succ ell, rfl⟩
  let a : AdmissibleKptNode family :=
    ⟨⟨ell, Q.restrict (Nat.le_succ ell)⟩, hAdA⟩
  let f := A.freeLevel ell
  have hf : f ≤ ell := A.freeLevel_le ell
  have hEllSize : ell < A.size := by
    have hvCut := A.freeLevel_le v
    omega
  have hAdParameter : IsAdmissibleRawType family
      (A.rawTypeAtFree ell) :=
    ⟨A, ell, hEllSize, hAvoid, rfl⟩
  let param : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree ell, hAdParameter⟩
  let p : List (AdmissibleKptNode family) :=
    if f = 0 then [] else [param]
  have hParameterType :
      Q.lastOrdinaryParameter f hf =
        A.partialTypeAt f ell :=
    partialTypeAt_lastOrdinaryParameter A v ell f hf
  have hParameterRecord :
      (⟨f, Q.lastOrdinaryParameter f hf⟩ :
        RawPartialTypeNode db du dd) = A.rawTypeAtFree ell := by
    change (⟨f, Q.lastOrdinaryParameter f hf⟩ :
      RawPartialTypeNode db du dd) =
      (⟨f, A.partialTypeAt f ell⟩ :
        RawPartialTypeNode db du dd)
    rw [hParameterType]
  have hParam :
      p.map (fun x => x.1) =
        (Q.canonicalParameterRecord f hf).toList := by
    by_cases hz : f = 0
    · simp [p, hz, PartialTypeWithE.canonicalParameterRecord]
    · have hh : [A.rawTypeAtFree ell] =
          [⟨f, Q.lastOrdinaryParameter f hf⟩] :=
        congrArg (fun x : RawPartialTypeNode db du dd => [x])
          hParameterRecord.symm
      simpa [p, hz, PartialTypeWithE.canonicalParameterRecord,
        param] using hh
  have hGate : f = 0 ∨ f < ell := by
    by_cases hz : f = 0
    · exact Or.inl hz
    · exact Or.inr (freeLevel_pos_lt_vertex A ell (by omega))
  have hValid : ValidNewOrdinaryColumn Q f :=
    validNewColumn_of_extracted_partialType A v ell hv (by omega)
  refine ⟨a, b, p, Q.terminalLetter, ?_, ?_, rfl, ?_⟩
  · exact ⟨ell, f, hf, Q, rfl, rfl, rfl,
      hValid, hParam, hGate⟩
  · exact canonicalKptStep_covBy family
      ⟨ell, f, hf, Q, rfl, rfl, rfl,
        hValid, hParam, hGate⟩
  · intro hPos
    have hNE : f ≠ 0 := by omega
    refine ⟨param, ?_, rfl⟩
    simp [p, hNE]

end SuccessorTree.V10
