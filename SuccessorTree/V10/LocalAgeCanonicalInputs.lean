import SuccessorTree.V10.LocalAgeNeutralParameter
import SuccessorTree.V10.CanonicalStepUniqueness
import Mathlib.Tactic

/-!
# Exact successor input data from ANY forbidden-free representation

The checked canonical Kpt successor graph has unique predecessor, parameter
and terminal letter. To prove neutral insertion preserves this successor,
we need the converse to its witness extraction: a source step whose target
is represented by an ambient (A,v) must have precisely the terminal
two-vertex L+ letter from (ordinary ell,v) and precisely the empty or
singleton canonical parameter from A's ordinary vertex ell.

This is proved by constructing that explicit canonical step in A and then
applying the already proved successor-input uniqueness. There is no new
axiom, no guessed parameter, and the positive/negative directed L and E
atomic data are the exact ambient records.

This is a local identification lemma. The forthcoming weak-successor
proof will apply it to A and its neutral-inserted image, using checked
preservation of the terminal letter and parameter list.
-/

namespace SuccessorTree.V10

/-- Source successor inputs are uniquely the ambient canonical ones.
Both the terminal letter and the whole empty-or-singleton parameter list
are obtained as conclusions from the genuine canonical successor graph. -/
theorem canonicalKptStep_inputs_of_ambient
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hFree : A.freeLevel v = ell + 1)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b)
    (hb : b.1 = A.rawTypeAtFree v) :
    let hEllSize : ell < A.size := by
      have h := A.freeLevel_le v
      omega
    let par : AdmissibleKptNode family :=
      ⟨A.rawTypeAtFree ell, ⟨A,ell,hEllSize,hAvoid,rfl⟩⟩
    c = (A.partialTypeAt (ell + 1) v).terminalLetter ∧
      p = if A.freeLevel ell = 0 then [] else [par] := by
  let Q : PartialTypeWithE (ell + 1) db du dd :=
    A.partialTypeAt (ell + 1) v
  have hEllSize : ell < A.size := by
    have h := A.freeLevel_le v
    omega
  have hRawB :
      (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd) =
      A.rawTypeAtFree v := by
    change
      (⟨ell + 1,A.partialTypeAt (ell+1) v⟩ :
        RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩ :
        RawPartialTypeNode db du dd)
    rw [hFree]
  have hAdB : IsAdmissibleRawType family
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) := by
    rw [hRawB]
    exact ⟨A,v,hv,hAvoid,rfl⟩
  let bE : AdmissibleKptNode family := ⟨⟨ell+1,Q⟩,hAdB⟩
  have hAdA : IsAdmissibleRawType family
      (⟨ell,Q.restrict (Nat.le_succ ell)⟩ :
        RawPartialTypeNode db du dd) :=
    admissibleRawType_of_prefix family hAdB
      ⟨Nat.le_succ ell,rfl⟩
  let aE : AdmissibleKptNode family :=
    ⟨⟨ell,Q.restrict (Nat.le_succ ell)⟩,hAdA⟩
  let f := A.freeLevel ell
  have hf : f ≤ ell := A.freeLevel_le ell
  let par : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree ell,⟨A,ell,hEllSize,hAvoid,rfl⟩⟩
  let pE : List (AdmissibleKptNode family) :=
    if f = 0 then [] else [par]
  have hParameterType :
      Q.lastOrdinaryParameter f hf = A.partialTypeAt f ell :=
    partialTypeAt_lastOrdinaryParameter A v ell f hf
  have hParameterRecord :
      (⟨f, Q.lastOrdinaryParameter f hf⟩ :
        RawPartialTypeNode db du dd) = A.rawTypeAtFree ell := by
    change
      (⟨f,Q.lastOrdinaryParameter f hf⟩ :
        RawPartialTypeNode db du dd) =
      (⟨f,A.partialTypeAt f ell⟩ :
        RawPartialTypeNode db du dd)
    rw [hParameterType]
  have hParam :
      pE.map (fun x => x.1) =
        (Q.canonicalParameterRecord f hf).toList := by
    by_cases hz : f = 0
    · simp [pE, hz, PartialTypeWithE.canonicalParameterRecord]
    · have hh : [A.rawTypeAtFree ell] =
          [(⟨f,Q.lastOrdinaryParameter f hf⟩ :
            RawPartialTypeNode db du dd)] :=
        congrArg (fun x : RawPartialTypeNode db du dd => [x])
          hParameterRecord.symm
      simpa [pE,hz,PartialTypeWithE.canonicalParameterRecord,par]
        using hh
  have hGate : f = 0 ∨ f < ell := by
    by_cases hz : f = 0
    · exact Or.inl hz
    · exact Or.inr (freeLevel_pos_lt_vertex A ell (by omega))
  have hValid : ValidNewOrdinaryColumn Q f :=
    validNewColumn_of_extracted_partialType A v ell hv (by omega)
  have hExpected :
      IsCanonicalKptStep family aE pE Q.terminalLetter bE :=
    ⟨ell,f,hf,Q,rfl,rfl,rfl,hValid,hParam,hGate⟩
  have hbEq : bE = b := by
    apply Subtype.ext
    exact hRawB.trans hb.symm
  have hExpectedB :
      IsCanonicalKptStep family aE pE Q.terminalLetter b := by
    simpa only [hbEq] using hExpected
  obtain ⟨_,hp,hc⟩ :=
    canonicalKptStep_inputs_unique family hStep hExpectedB
  exact ⟨hc,hp⟩

end SuccessorTree.V10
