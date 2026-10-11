import SuccessorTree.V10.M3MiddleParameter
import SuccessorTree.V10.LocalAgeCanonicalInputs
import Mathlib.Tactic

/-!
# The actual finite middle clone gives a genuine canonical Kpt cover

For every forbidden-free A, source type vertex v at free cut ell, and
old ordinary n<ell, the gated middle-clone B is forbidden-free. Its
shifted type vertex has cut ell+1, its full predecessor is the source,
its terminal Sigma-letter is the earlier crossing's letter, and its
canonical empty-or-singleton parameter list is likewise the earlier
crossing's list.

These properties are proved for the EXISTING IsCanonicalKptStep graph,
not for an abstract successor relation assumed to exist. This is the
finite-existence ingredient of M3; independence from the choice of
A and v will be obtained by the already checked functional S-tree
successor once its canonical inputs are fixed from the source record.
-/

namespace SuccessorTree.V10

/-- The genuine gated middle insertion exhibits a canonical
one-step Kpt successor with exactly the earlier crossing's canonical
parameter list and terminal L+ letter. No new age or E assumption. -/
theorem middleCloneInsertPartial_canonicalStep
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell n : Nat) (hell : ell ≤ A.size) (hn : n < ell)
    (v : Nat) (hv : v < A.size)
    (hOldFree : A.freeLevel v = ell)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    let B := middleCloneInsertPartial A ell n hell hn
    let a : AdmissibleKptNode family :=
      ⟨A.rawTypeAtFree v,⟨A,v,hv,hAvoid,rfl⟩⟩
    let hIns : IsLInsertion A B ell :=
      middleCloneInsertPartial_isLInsertion A ell n hell hn
    let hvB : insertAddress ell v < B.size := by
      rw [hIns.size_eq]
      by_cases hlt : v < ell
      · rw [insertAddress_below ell v hlt]
        omega
      · rw [insertAddress_above ell v (by omega)]
        omega
    let hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
      middleCloneInsertPartial_preserves_avoidance
        family A ell n hell hn hAvoid
    let b : AdmissibleKptNode family :=
      ⟨B.rawTypeAtFree (insertAddress ell v),
        ⟨B,insertAddress ell v,hvB,hAvoidB,rfl⟩⟩
    ∃ (p : List (AdmissibleKptNode family))
      (c : RawKptLetter db du dd),
      IsCanonicalKptStep family a p c b ∧
      p.map Subtype.val =
        ((A.partialTypeAt (n+1) v).canonicalParameterRecord
          (A.freeLevel n) (A.freeLevel_le n)).toList ∧
      c = (A.partialTypeAt (n+1) v).terminalLetter := by
  let B := middleCloneInsertPartial A ell n hell hn
  let a : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree v,⟨A,v,hv,hAvoid,rfl⟩⟩
  have hIns : IsLInsertion A B ell :=
    middleCloneInsertPartial_isLInsertion A ell n hell hn
  have hvB : insertAddress ell v < B.size := by
    rw [hIns.size_eq]
    by_cases hlt : v < ell
    · rw [insertAddress_below ell v hlt]
      omega
    · rw [insertAddress_above ell v (by omega)]
      omega
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    middleCloneInsertPartial_preserves_avoidance
      family A ell n hell hn hAvoid
  let b : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell v),
      ⟨B,insertAddress ell v,hvB,hAvoidB,rfl⟩⟩
  have hBFree : B.freeLevel (insertAddress ell v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      A ell n hell hn v hv hOldFree
  have haRaw : a.1 =
      (⟨ell,A.partialTypeAt ell v⟩ : RawPartialTypeNode db du dd) := by
    change (⟨A.freeLevel v,A.partialTypeAt (A.freeLevel v) v⟩ :
      RawPartialTypeNode db du dd) =
      (⟨ell,A.partialTypeAt ell v⟩ : RawPartialTypeNode db du dd)
    rw [hOldFree]
  have hbRaw : b.1 =
      (⟨ell+1,B.partialTypeAt (ell+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    change (⟨B.freeLevel (insertAddress ell v),
      B.partialTypeAt (B.freeLevel (insertAddress ell v))
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd) =
      (⟨ell+1,B.partialTypeAt (ell+1)
        (insertAddress ell v)⟩ : RawPartialTypeNode db du dd)
    rw [hBFree]
  have hRawPrefix : a.1 ≤ b.1 := by
    rw [haRaw,hbRaw]
    exact ⟨Nat.le_succ ell,
      (middleCloneInsertPartial_target_restrict A ell n
        hell hn v hv).symm⟩
  have hCover : a ⋖ b := by
    have hPrefix : a ≤ b := hRawPrefix
    apply LevelTree.covBy_of_le_level_succ hPrefix
    change b.1.1 = a.1.1 + 1
    rw [haRaw,hbRaw]
  obtain ⟨p,c,hStep⟩ :=
    canonicalKptStep_exists_of_covBy family hCover
  have hInputs := canonicalKptStep_inputs_of_ambient
    family B (insertAddress ell v) ell hvB hAvoidB
    hBFree hStep rfl
  have hLetter : c = (A.partialTypeAt (n+1) v).terminalLetter := by
    exact hInputs.1.trans
      (middleCloneInsertPartial_terminalLetter_eq
        A ell n hell hn v hv hOldFree)
  let d := A.freeLevel n
  have hd : d ≤ n := A.freeLevel_le n
  have hdEll : d ≤ ell := hd.trans (Nat.le_of_lt hn)
  have hFreeClone : B.freeLevel ell = d :=
    middleCloneInsertPartial_new_freeLevel A ell n hell hn
  have hParFull := partialTypeAt_lastOrdinaryParameter
    B (insertAddress ell v) ell d hdEll
  have hParRaw : B.rawTypeAtFree ell =
      (⟨d,(B.partialTypeAt (ell+1) (insertAddress ell v)).lastOrdinaryParameter d hdEll⟩ :
        RawPartialTypeNode db du dd) := by
    change (⟨B.freeLevel ell,B.partialTypeAt (B.freeLevel ell) ell⟩ :
      RawPartialTypeNode db du dd) = _
    rw [hFreeClone]
    exact congrArg (Sigma.mk d) hParFull.symm
  have hParMap :
      p.map Subtype.val =
        ((B.partialTypeAt (ell+1) (insertAddress ell v)).canonicalParameterRecord d hdEll).toList := by
    rw [hInputs.2]
    by_cases hz : d = 0
    · simp [hFreeClone, hz, PartialTypeWithE.canonicalParameterRecord]
    · simp [hFreeClone, hz, PartialTypeWithE.canonicalParameterRecord,
        hParRaw]
  have hParFinal : p.map Subtype.val =
      ((A.partialTypeAt (n+1) v).canonicalParameterRecord d hd).toList :=
    hParMap.trans
      (middleCloneInsertPartial_parameterList_eq A ell n hell hn v)
  exact ⟨p,c,hStep,hParFinal,hLetter⟩

end SuccessorTree.V10
