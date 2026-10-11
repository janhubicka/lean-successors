import SuccessorTree.V10.M3TotalPrescription
import SuccessorTree.V10.M3StepInputB3
import SuccessorTree.V10.M3MiddleCanonicalStep
import SuccessorTree.V10.PrescribedBoringCompletion
import Mathlib.Tactic

/-!
# Corrected M3-B3 for the *actual* total finite-witness prescription

Unlike the earlier conditional clone lemmas, this theorem takes the
specific PrescribedBoringData constructed by choosing a forbidden-free
finite witness for each admissible source T. The actual E3-gated
middle-clone insertion is a valid finite partial structure, remains
forbidden-free, and its new target is an admissible full L+ type.

For the chosen finite witness A,v, the old n-th crossing and the
new ell-th crossing have the SAME actual canonical parameter list
and terminal Sigma letter. The lower cut is allowed to vary with T.
Those two verified finite record identities discharge the exact
finite L-only corrected B3 test via the independently formalized
irreducible clone projection. No new age hypothesis or abstract
successor preservation axiom is introduced.

Combining this with the actual B1/B2 prescription and target
admissibility yields an explicit normalized one-gap ShapeMap.
The manuscript's separate M3 duplication/factorization clause and
the original language adapter still require comparison.
-/

namespace SuccessorTree.V10

/-- The chosen genuine E3-gated total middle-duplication function
satisfies the CORRECTED finite L-age B3, without assuming it. -/
theorem m3TotalBoringData_correctedB3
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell) :
    (m3TotalBoringData family ell n hn).CorrectedB3 family := by
  let F := m3TotalBoringData family ell n hn
  apply F.correctedB3_of_repeated_canonical_inputs family n hn
  intro T hT
  have hAd : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) := by
    exact hT
  let W := chooseM3Witness family T hAd
  let B := middleCloneInsertPartial W.A ell n W.ell_le_size hn
  let d := W.A.freeLevel n
  have hd : d ≤ n := W.A.freeLevel_le n
  have hdEll : d ≤ ell := hd.trans (Nat.le_of_lt hn)
  have hTRecord : T = W.A.partialTypeAt ell W.v :=
    record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
  have hOldRecord :
      T.restrict (Nat.succ_le_of_lt hn) =
        W.A.partialTypeAt (n+1) W.v := by
    rw [hTRecord]
    exact W.A.partialTypeAt_restrict (n+1) ell W.v
      (Nat.succ_le_of_lt hn)
  have hOldValid : ValidNewOrdinaryColumn
      (W.A.partialTypeAt (n+1) W.v) d := by
    exact validNewColumn_of_extracted_partialType W.A W.v
      n W.hv (by rw [W.freeLevel_eq]; omega)
  have hOutput :
      F.target T = B.partialTypeAt (ell+1) (insertAddress ell W.v) := by
    change (if hh : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
      m3FiniteTarget family n hn T hh
      else m3UnusedTarget ell db du dd) =
        B.partialTypeAt (ell+1) (insertAddress ell W.v)
    rw [dif_pos hAd]
    rfl
  have hBV : insertAddress ell W.v < B.size := by
    have hIns := middleCloneInsertPartial_isLInsertion
      W.A ell n W.ell_le_size hn
    rw [hIns.size_eq]
    by_cases hlt : W.v < ell
    · rw [insertAddress_below ell W.v hlt]
      omega
    · rw [insertAddress_above ell W.v (by omega)]
      omega
  have hBVFree : B.freeLevel (insertAddress ell W.v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      W.A ell n W.ell_le_size hn W.v W.hv W.freeLevel_eq
  have hNewValid : ValidNewOrdinaryColumn (F.target T) d := by
    rw [hOutput]
    have hValid := validNewColumn_of_extracted_partialType
      B (insertAddress ell W.v) ell hBV (by rw [hBVFree])
    have hCut : B.freeLevel ell = d :=
      middleCloneInsertPartial_new_freeLevel
        W.A ell n W.ell_le_size hn
    rw [hCut] at hValid
    exact hValid
  have hNewParam :
      ((F.target T).canonicalParameterRecord d hdEll).toList =
      ((W.A.partialTypeAt (n+1) W.v).canonicalParameterRecord d hd).toList := by
    rw [hOutput]
    exact middleCloneInsertPartial_parameterList_eq
      W.A ell n W.ell_le_size hn W.v
  have hNewLetter :
      (F.target T).terminalLetter =
        (W.A.partialTypeAt (n+1) W.v).terminalLetter := by
    rw [hOutput]
    exact middleCloneInsertPartial_terminalLetter_eq
      W.A ell n W.ell_le_size hn W.v W.hv W.freeLevel_eq
  let oldQ := W.A.partialTypeAt (n+1) W.v
  let p := (oldQ.canonicalParameterRecord d hd).toList
  let c := oldQ.terminalLetter
  refine ⟨p,c,?_,?_⟩
  · rw [hOldRecord]
    exact ⟨d,hd,hOldValid,rfl,rfl⟩
  · exact ⟨d,hdEll,hNewValid,hNewParam,hNewLetter.symm⟩

/-- An explicit normalized one-gap shape-preserving map realizing
the actual M3 middle-duplication prescription on every admissible
level-ell type, with no B3 premise added to the M3 hypotheses. -/
theorem m3TotalBoringData_boring_extension_exists
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell) :
    let F := m3TotalBoringData family ell n hn
    ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
      Φ ∈ KptM family ∧ Φ.SkipsOnly ell ∧
      ∀ (T : PartialTypeWithE ell db du dd)
        (hSrc : T ∈ F.source)
        (hAdT : IsAdmissibleRawType family
          (⟨ell,T⟩ : RawPartialTypeNode db du dd)),
        (Φ (⟨⟨ell,T⟩,hAdT⟩ : AdmissibleKptNode family)).1 =
          (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) := by
  let F := m3TotalBoringData family ell n hn
  exact F.prescribedKpt_boring_extension_exists family
    (m3TotalBoringData_correctedB3 family n hn)
    (fun T hT =>
      m3TotalBoringData_target_admissible family n hn T hT)
    (by omega)

end SuccessorTree.V10
