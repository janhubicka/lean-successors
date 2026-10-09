import SuccessorTree.V10.CanonicalStepGraph
import Mathlib.Tactic

/-!
# Realizing a canonical Kpt successor from every genuine ambient type

A node of the admissible Kpt forest has, by its definition, a
forbidden-free partial-structure witness A and an ordinary vertex v
whose free E cut is its level. If that level is ell+1, the one-step
cover is obtained by truncating at ell.

This module constructs the EXACT successor inputs from such a
witness: the predecessor, the empty or positive-singleton canonical
parameter coming from the *new* ordinary vertex ell, and the
two-vertex terminal L+ Sigma letter (ell,t). The proof checks that
every new E pair and all directed L relations obey the no-new-tuples
rule. It also proves that the step is a cover.

No forward S function or admissible-Sigma restriction is assumed.
The next theorem will compare the constructed predecessor to any
other immediate predecessor of the same target, giving S3.
-/

namespace SuccessorTree.V10

/-- A represented Kpt type of level ell+1 has an actual canonical
one-step predecessor and the exact empty-or-positive-singleton
parameter required in Definition 6.30. -/
theorem exists_canonical_step_from_ambient
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hFree : A.freeLevel v = ell + 1) :
    ∃ (a b : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : RawKptLetter db du dd),
      IsCanonicalKptStep family a p c b ∧
      a ⋖ b ∧
      b.1 = (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
        RawPartialTypeNode db du dd) := by
  let Q : PartialTypeWithE (ell + 1) db du dd :=
    A.partialTypeAt (ell + 1) v
  have hRawB :
      (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) =
        A.rawTypeAtFree v := by
    change (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
      RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v,
        A.partialTypeAt (A.freeLevel v) v⟩ :
          RawPartialTypeNode db du dd)
    rw [hFree]
  have hAdB : IsAdmissibleRawType family
      (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) := by
    rw [hRawB]
    exact ⟨A, v, hv, hAvoid, rfl⟩
  let b : AdmissibleKptNode family :=
    ⟨⟨ell + 1, Q⟩, hAdB⟩
  have hAdA : IsAdmissibleRawType family
      (⟨ell, Q.restrict (Nat.le_succ ell)⟩ :
        RawPartialTypeNode db du dd) := by
    exact admissibleRawType_of_prefix family hAdB
      ⟨Nat.le_succ ell, rfl⟩
  let a : AdmissibleKptNode family :=
    ⟨⟨ell, Q.restrict (Nat.le_succ ell)⟩, hAdA⟩
  let f := A.freeLevel ell
  have hf : f ≤ ell := A.freeLevel_le ell
  have hEllSize : ell < A.size := by
    have hvCut := A.freeLevel_le v
    dsimp [f] at hf
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
  have hValid : ValidNewOrdinaryColumn Q f := by
    exact validNewColumn_of_extracted_partialType A v ell hv
      (by omega)
  refine ⟨a, b, p, Q.terminalLetter, ?_, ?_, rfl⟩
  · exact ⟨ell, f, hf, Q, rfl, rfl, rfl,
      hValid, hParam, hGate⟩
  · exact canonicalKptStep_covBy family
      ⟨ell, f, hf, Q, rfl, rfl, rfl,
        hValid, hParam, hGate⟩

end SuccessorTree.V10
