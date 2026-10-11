import SuccessorTree.V10.M3ActualCorrectedB3
import SuccessorTree.V10.M3MiddleCanonicalStep
import SuccessorTree.V10.CanonicalRawSTree
import Mathlib.Tactic

/-!
# The actual total M3 target repeats the old n-th canonical successor

For every admissible level-ell source T and n<ell, the selected
finite witness W produces an ACTUAL canonical Kpt successor at the
inserted coordinate ell. Its empty/singleton parameter list and
terminal L+ Sigma letter are precisely the canonical inputs of the
old crossing at ordinary coordinate n in T.

We verify that this old crossing is also a genuine admissible
canonical Kpt step on the original source's shorter prefixes.
Uniqueness of the forward successor then shows that the chosen
M3 target equals S(a,p_n,c_n), rather than merely sharing its L-age.

No extra source or finite-witness compatibility hypotheses are
introduced. The full B1/B2/finite-B3 construction is in the imports.
-/

namespace SuccessorTree.V10

/-- The selected total M3 prescribed target at any admissible source
is the actual canonical successor using the SAME p,c as the old
n-th crossing. Both steps are legitimate Kpt steps, not invented
two-vertex records. -/
theorem m3TotalBoringData_uses_old_canonical_step
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    let F := m3TotalBoringData family ell n hn
    let aNew : AdmissibleKptNode family :=
      ⟨⟨ell,T⟩,hAd⟩
    ∃ (aOld bOld bNew : AdmissibleKptNode family)
      (p : List (AdmissibleKptNode family))
      (c : RawKptLetter db du dd),
      IsCanonicalKptStep family aOld p c bOld ∧
      bOld.1 =
        (⟨n+1,T.restrict (Nat.succ_le_of_lt hn)⟩ :
          RawPartialTypeNode db du dd) ∧
      canonicalKptSucc family aNew p c = some bNew ∧
      bNew.1 =
        (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) := by
  classical
  let F := m3TotalBoringData family ell n hn
  let aNew : AdmissibleKptNode family := ⟨⟨ell,T⟩,hAd⟩
  let W := chooseM3Witness family T hAd
  let B := middleCloneInsertPartial W.A ell n W.ell_le_size hn
  have hIns : IsLInsertion W.A B ell :=
    middleCloneInsertPartial_isLInsertion
      W.A ell n W.ell_le_size hn
  have hBV : insertAddress ell W.v < B.size := by
    have hv := W.hv
    rw [hIns.size_eq]
    by_cases hlt : W.v < ell
    · rw [insertAddress_below ell W.v hlt]
      omega
    · rw [insertAddress_above ell W.v (by omega)]
      omega
  have hBAvoid : ∀ bad, bad ∈ family → bad.Avoids B.L :=
    middleCloneInsertPartial_preserves_avoidance
      family W.A ell n W.ell_le_size hn W.avoids
  let a1 : AdmissibleKptNode family :=
    ⟨W.A.rawTypeAtFree W.v,⟨W.A,W.v,W.hv,W.avoids,rfl⟩⟩
  let b1 : AdmissibleKptNode family :=
    ⟨B.rawTypeAtFree (insertAddress ell W.v),
      ⟨B,insertAddress ell W.v,hBV,hBAvoid,rfl⟩⟩
  obtain ⟨p,c,hNewStep,hPar,hLetter⟩ :=
    middleCloneInsertPartial_canonicalStep family W.A ell n
      W.ell_le_size hn W.v W.hv W.freeLevel_eq W.avoids
  have hNewStep' : IsCanonicalKptStep family a1 p c b1 :=
    hNewStep
  let oldQ := W.A.partialTypeAt (n+1) W.v
  let d := W.A.freeLevel n
  have hd : d ≤ n := W.A.freeLevel_le n
  have hQOld : T.restrict (Nat.succ_le_of_lt hn) = oldQ := by
    have hT : T = W.A.partialTypeAt ell W.v :=
      record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
    calc
      T.restrict (Nat.succ_le_of_lt hn) =
          (W.A.partialTypeAt ell W.v).restrict
            (Nat.succ_le_of_lt hn) :=
        congrArg
          (fun Q : PartialTypeWithE ell db du dd =>
            Q.restrict (Nat.succ_le_of_lt hn)) hT
      _ = oldQ :=
        W.A.partialTypeAt_restrict (n+1) ell W.v
          (Nat.succ_le_of_lt hn)
  have hOldAd : IsAdmissibleRawType family
      (⟨n+1,oldQ⟩ : RawPartialTypeNode db du dd) := by
    have hPrefix := admissibleRawType_closed_under_prefix
      family hAd (n+1) (Nat.succ_le_of_lt hn)
    rw [hQOld] at hPrefix
    exact hPrefix
  have hOldBaseAd : IsAdmissibleRawType family
      (⟨n,oldQ.restrict (Nat.le_succ n)⟩ :
        RawPartialTypeNode db du dd) :=
    admissibleRawType_closed_under_prefix family hOldAd
      n (Nat.le_succ n)
  let aOld : AdmissibleKptNode family :=
    ⟨⟨n,oldQ.restrict (Nat.le_succ n)⟩,hOldBaseAd⟩
  let bOld : AdmissibleKptNode family :=
    ⟨⟨n+1,oldQ⟩,hOldAd⟩
  have hValid : ValidNewOrdinaryColumn oldQ d :=
    validNewColumn_of_extracted_partialType
      W.A W.v n W.hv (by rw [W.freeLevel_eq]; omega)
  have hGate : d = 0 ∨ d < n := by
    by_cases hz : d = 0
    · exact Or.inl hz
    · exact Or.inr (freeLevel_pos_lt_vertex W.A n (by omega))
  have hOldStep : IsCanonicalKptStep family aOld p c bOld :=
    ⟨n,d,hd,oldQ,rfl,rfl,hLetter,hValid,hPar,hGate⟩
  have hOldRaw : bOld.1 =
      (⟨n+1,T.restrict (Nat.succ_le_of_lt hn)⟩ :
        RawPartialTypeNode db du dd) :=
    congrArg (Sigma.mk (n+1)) hQOld.symm
  have haNew : aNew = a1 :=
    Subtype.ext W.raw_eq
  have hOutput :
      F.target T =
        B.partialTypeAt (ell+1) (insertAddress ell W.v) := by
    change (if hh : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
        m3FiniteTarget family n hn T hh
      else m3UnusedTarget ell db du dd) =
        B.partialTypeAt (ell+1) (insertAddress ell W.v)
    rw [dif_pos hAd]
    rfl
  have hBFree : B.freeLevel (insertAddress ell W.v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      W.A ell n W.ell_le_size hn W.v W.hv W.freeLevel_eq
  have hNewRaw : b1.1 =
      (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) := by
    change B.rawTypeAtFree (insertAddress ell W.v) =
      (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd)
    change (⟨B.freeLevel (insertAddress ell W.v),
      B.partialTypeAt (B.freeLevel (insertAddress ell W.v))
        (insertAddress ell W.v)⟩ : RawPartialTypeNode db du dd) =
      (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd)
    rw [hBFree,hOutput]
  refine ⟨aOld,bOld,b1,p,c,hOldStep,hOldRaw,?_,hNewRaw⟩
  rw [haNew]
  exact canonicalKptSucc_eq_some_of_step family hNewStep'

end SuccessorTree.V10
