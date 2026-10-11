import SuccessorTree.V10.M3TotalPrescription
import SuccessorTree.V10.EmptyParameterS2
import SuccessorTree.V10.M3MiddleLetter
import SuccessorTree.V10.M3MiddleParameter
import SuccessorTree.V10.M3OrdinaryCoherence
import Mathlib.Tactic

/-!
# The actual M3 prescribed target is independent of finite representations

The previous M3 total prescription chooses a forbidden-free witness
(A,v) of the source type using Classical.choice. This choice is not an
additional mathematical premise, but the manuscript requires the
resulting duplication f(T) to be intrinsic to T.

Two such witnesses yield actual E3-gated middle insertions with the
same complete old predecessor; the old ordinary E-socle determines
the same free cut for n. The inserted shortened parameter records
and full terminal Sigma letters both agree with the earlier n-th
crossings of the respective old types, which themselves are equal.
The *proved* finite S2 uniqueness theorem therefore identifies the
ENTIRE new L+ target records, including every auxiliary E bit.

No new source compatibility/age hypothesis or abstract successor law
is assumed. This is stronger than the B2 equality of ordinary socles.
-/

namespace SuccessorTree.V10

private theorem m3_option_toList_injective {α : Type*}
    {x y : Option α} (h : x.toList = y.toList) : x = y := by
  cases x <;> cases y <;> simp_all

/-- Inserting the same ordinary clone n<ell into any two represented
finite partial structures with the SAME complete source L+ record
produces the SAME complete level-(ell+1) target type.
This includes every directed missing L tuple and every E atom. -/
theorem middleCloneInsertPartial_type_independent
    {db du dd : Nat}
    (A C : EnumeratedPartialStructure db du dd)
    (ell n v w : Nat)
    (hellA : ell ≤ A.size) (hellC : ell ≤ C.size)
    (hn : n < ell)
    (hv : v < A.size) (hw : w < C.size)
    (hFreeA : A.freeLevel v = ell)
    (hFreeC : C.freeLevel w = ell)
    (hSource : A.partialTypeAt ell v = C.partialTypeAt ell w) :
    (middleCloneInsertPartial A ell n hellA hn).partialTypeAt
        (ell+1) (insertAddress ell v) =
    (middleCloneInsertPartial C ell n hellC hn).partialTypeAt
        (ell+1) (insertAddress ell w) := by
  let B := middleCloneInsertPartial A ell n hellA hn
  let H := middleCloneInsertPartial C ell n hellC hn
  let d := A.freeLevel n
  have hd : d ≤ n := A.freeLevel_le n
  have hdEll : d ≤ ell := hd.trans (Nat.le_of_lt hn)
  have hComp : SameOrdinaryAtCut
      (A.partialTypeAt ell v) (C.partialTypeAt ell w) := by
    rw [hSource]
    exact sameOrdinaryAtCut_refl _
  have hCut : A.freeLevel n = C.freeLevel n :=
    sameOrdinaryAtCut_oldFreeLevel_eq A C v w n hn hComp
  have hQOld :
      A.partialTypeAt (n+1) v = C.partialTypeAt (n+1) w := by
    calc
      A.partialTypeAt (n+1) v =
          (A.partialTypeAt ell v).restrict (Nat.succ_le_of_lt hn) :=
        (A.partialTypeAt_restrict (n+1) ell v
          (Nat.succ_le_of_lt hn)).symm
      _ = (C.partialTypeAt ell w).restrict (Nat.succ_le_of_lt hn) :=
        congrArg (fun T : PartialTypeWithE ell db du dd =>
          T.restrict (Nat.succ_le_of_lt hn)) hSource
      _ = C.partialTypeAt (n+1) w :=
        C.partialTypeAt_restrict (n+1) ell w
          (Nat.succ_le_of_lt hn)
  have hvB : insertAddress ell v < B.size := by
    have hvOld := hv
    have hh := middleCloneInsertPartial_isLInsertion A ell n hellA hn
    rw [hh.size_eq]
    by_cases hlt : v < ell
    · rw [insertAddress_below ell v hlt]
      omega
    · rw [insertAddress_above ell v (by omega)]
      omega
  have hwH : insertAddress ell w < H.size := by
    have hwOld := hw
    have hh := middleCloneInsertPartial_isLInsertion C ell n hellC hn
    rw [hh.size_eq]
    by_cases hlt : w < ell
    · rw [insertAddress_below ell w hlt]
      omega
    · rw [insertAddress_above ell w (by omega)]
      omega
  have hBFree : B.freeLevel (insertAddress ell v) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      A ell n hellA hn v hv hFreeA
  have hHFree : H.freeLevel (insertAddress ell w) = ell+1 :=
    middleCloneInsertPartial_prescribed_vertex_freeLevel
      C ell n hellC hn w hw hFreeC
  have hBValid : ValidNewOrdinaryColumn
      (B.partialTypeAt (ell+1) (insertAddress ell v)) d := by
    have hh := validNewColumn_of_extracted_partialType
      B (insertAddress ell v) ell hvB (by rw [hBFree])
    have hNew := middleCloneInsertPartial_new_freeLevel
      A ell n hellA hn
    rw [hNew] at hh
    exact hh
  have hHValid : ValidNewOrdinaryColumn
      (H.partialTypeAt (ell+1) (insertAddress ell w)) d := by
    have hh := validNewColumn_of_extracted_partialType
      H (insertAddress ell w) ell hwH (by rw [hHFree])
    have hNew := middleCloneInsertPartial_new_freeLevel
      C ell n hellC hn
    rw [hNew, ←hCut] at hh
    exact hh
  have hOld :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).restrict
        (Nat.le_succ ell) =
      (H.partialTypeAt (ell+1) (insertAddress ell w)).restrict
        (Nat.le_succ ell) := by
    calc
      _ = A.partialTypeAt ell v :=
        middleCloneInsertPartial_target_restrict
          A ell n hellA hn v hv
      _ = C.partialTypeAt ell w := hSource
      _ = _ :=
        (middleCloneInsertPartial_target_restrict
          C ell n hellC hn w hw).symm
  have hParamA :
      ((B.partialTypeAt (ell+1) (insertAddress ell v)).canonicalParameterRecord
        d hdEll).toList =
      ((A.partialTypeAt (n+1) v).canonicalParameterRecord
        d hd).toList :=
    middleCloneInsertPartial_parameterList_eq A ell n hellA hn v
  have hParamC :
      ((H.partialTypeAt (ell+1) (insertAddress ell w)).canonicalParameterRecord
        d hdEll).toList =
      ((C.partialTypeAt (n+1) w).canonicalParameterRecord
        d hd).toList := by
    have hh := middleCloneInsertPartial_parameterList_eq
      C ell n hellC hn w
    simpa only [←hCut] using hh
  have hLists :
      ((B.partialTypeAt (ell+1) (insertAddress ell v)).canonicalParameterRecord
        d hdEll).toList =
      ((H.partialTypeAt (ell+1) (insertAddress ell w)).canonicalParameterRecord
        d hdEll).toList := by
    calc
      _ = ((A.partialTypeAt (n+1) v).canonicalParameterRecord
        d hd).toList := hParamA
      _ = ((C.partialTypeAt (n+1) w).canonicalParameterRecord
        d hd).toList := by rw [hQOld]
      _ = _ := hParamC.symm
  have hOptions :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).canonicalParameterRecord
        d hdEll =
      (H.partialTypeAt (ell+1) (insertAddress ell w)).canonicalParameterRecord
        d hdEll :=
    m3_option_toList_injective hLists
  have hLetter :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).terminalLetter =
      (H.partialTypeAt (ell+1) (insertAddress ell w)).terminalLetter := by
    calc
      _ = (A.partialTypeAt (n+1) v).terminalLetter :=
        middleCloneInsertPartial_terminalLetter_eq A ell n
          hellA hn v hv hFreeA
      _ = (C.partialTypeAt (n+1) w).terminalLetter :=
        congrArg (fun T : PartialTypeWithE (n+1) db du dd =>
          T.terminalLetter) hQOld
      _ = _ :=
        (middleCloneInsertPartial_terminalLetter_eq C ell n
          hellC hn w hw hFreeC).symm
  exact complete_successor_unique_of_option_parameter
    (B.partialTypeAt (ell+1) (insertAddress ell v))
    (H.partialTypeAt (ell+1) (insertAddress ell w))
    d hdEll hOld hBValid hHValid hOptions hLetter

/-- The finite-witness choice used by m3FiniteTarget is harmless:
the total prescribed output agrees with the insertion performed in
ANY finite forbidden-free representative of the same admissible T. -/
theorem m3FiniteTarget_eq_of_representation
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRaw : (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
      A.rawTypeAtFree v) :
    let hell : ell ≤ A.size := by
      have h := congrArg Sigma.fst hRaw
      have hh := A.freeLevel_le v
      change ell = A.freeLevel v at h
      omega
    m3FiniteTarget family n hn T hT =
      (middleCloneInsertPartial A ell n hell hn).partialTypeAt
        (ell+1) (insertAddress ell v) := by
  let W := chooseM3Witness family T hT
  have hFreeA : A.freeLevel v = ell := by
    have hh := congrArg Sigma.fst hRaw
    change ell = A.freeLevel v at hh
    exact hh.symm
  have hell : ell ≤ A.size := by
    have hh := A.freeLevel_le v
    omega
  have hFromW : T = W.A.partialTypeAt ell W.v :=
    record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
  have hFromA : T = A.partialTypeAt ell v :=
    record_eq_of_rawTypeAtFree T A v hRaw
  have hSources :
      W.A.partialTypeAt ell W.v = A.partialTypeAt ell v :=
    hFromW.symm.trans hFromA
  change (middleCloneInsertPartial W.A ell n W.ell_le_size hn).partialTypeAt
      (ell+1) (insertAddress ell W.v) =
    (middleCloneInsertPartial A ell n hell hn).partialTypeAt
      (ell+1) (insertAddress ell v)
  exact middleCloneInsertPartial_type_independent W.A A ell n
    W.v v W.ell_le_size hell hn W.hv hv W.freeLevel_eq
    hFreeA hSources

end SuccessorTree.V10
