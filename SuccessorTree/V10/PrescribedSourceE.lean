import SuccessorTree.V10.PrescribedSourceValues
import SuccessorTree.V10.PrescribedETransport
import Mathlib.Tactic

/-!
# The auxiliary E record at the prescribed source value

The complete L-reduct is checked separately. Here we compare every
E pair in the actual inserted structure with the genuine admissible
prescribed target f(S). The comparison includes the distinguished
type coordinate, both directions at the new ordinary vertex, all
old-old pairs and loops. The target is admissible, so the final
E-socle and reverse/loop facts are DERIVED from its finite witness.

No arbitrary "E-age witness" is imposed on corrected B3.
-/

namespace SuccessorTree.V10

/-- The literal prescribed insertion reproduces the ENTIRE E part
of f(type_A^ell(v)) when this source is prescribed and its actual
free level is ell. The source target's admissibility supplies the
correct final E-socle; no further E-compatibility axiom is needed. -/
theorem PrescribedBoringData.prescribedInsertPartial_source_E
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hFree : A.freeLevel v = ell)
    (hSrc : A.partialTypeAt ell v ∈ F.source)
    (hTargetAd : IsAdmissibleRawType family
      (⟨ell+1,F.target (A.partialTypeAt ell v)⟩ :
        RawPartialTypeNode db du dd))
    (k : Nat)
    (hValid : ValidNewOrdinaryColumn
      (F.target (A.partialTypeAt ell v)) k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell) :
    ∀ x y : Option (Fin (ell+1)),
      ((prescribedInsertPartial A
        (F.target (A.partialTypeAt ell v)) k hValid
        hell hPos hk hGate (F.upperIncoming A)
        (F.upperOutgoing A)).partialTypeAt (ell+1)
        (insertAddress ell v)).eRelation x y =
      (F.target (A.partialTypeAt ell v)).eRelation x y := by
  let S := A.partialTypeAt ell v
  let Q := F.target S
  let B := prescribedInsertPartial A Q k hValid hell hPos
    hk hGate (F.upperIncoming A) (F.upperOutgoing A)
  have hReach : ell ≤ A.freeLevel v := by omega
  have hBFree : B.freeLevel (insertAddress ell v) = ell+1 := by
    have h := prescribedInsertPartial_old_freeLevel A Q k hValid
      hell hPos hk hGate (F.upperIncoming A) (F.upperOutgoing A)
      v hv
    have hn : ¬ A.freeLevel v < ell := Nat.not_lt.mpr hReach
    rw [if_neg hn,hFree] at h
    exact h
  obtain ⟨W,w,hw,hAvoidW,hRawW⟩ := hTargetAd
  have hWFree : W.freeLevel w = ell+1 := by
    have hh := congrArg Sigma.fst hRawW
    change ell+1 = W.freeLevel w at hh
    omega
  have hQW : Q = W.partialTypeAt (ell+1) w :=
    record_eq_of_rawTypeAtFree Q W w hRawW
  have hQFull (i : Fin (ell+1)) :
      Q.eRelation (some i) none = true := by
    rw [hQW]
    exact W.partialTypeAt_fullESocle (ell+1) w
      (by omega) i
  have hQRev (i : Fin (ell+1)) :
      Q.eRelation none (some i) = false := by
    rw [hQW]
    exact W.partialTypeAt_no_reverseE (ell+1) w
      (by omega) i
  have hQLoop : Q.eRelation none none = false := by
    rw [hQW]
    exact W.partialTypeAt_no_typeE_loop (ell+1) w
  have hQOrdLoop :
      Q.eRelation (some (Fin.last ell))
        (some (Fin.last ell)) = false := by
    rw [hQW]
    change W.E ell ell = false
    cases he : W.E ell ell with
    | false => rfl
    | true =>
      have hlt := (W.E_inside ell ell he).1
      omega
  have hQOld (i j : Fin ell) :
      Q.eRelation (some i.castSucc) (some j.castSucc) =
        A.E i.val j.val := by
    have he := congrArg
      (fun T : PartialTypeWithE ell db du dd =>
        T.eRelation (some i) (some j))
      (F.extendsSource S hSrc)
    change Q.eRelation (some i.castSucc) (some j.castSucc) =
      A.E i.val j.val at he
    exact he
  have hBTypeLoop :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).eRelation
        none none = false :=
    B.partialTypeAt_no_typeE_loop (ell+1) (insertAddress ell v)
  have hBRev (i : Fin (ell+1)) :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).eRelation
        none (some i) = false :=
    B.partialTypeAt_no_reverseE (ell+1) (insertAddress ell v)
      (by omega) i
  have hBFull (i : Fin (ell+1)) :
      (B.partialTypeAt (ell+1) (insertAddress ell v)).eRelation
        (some i) none = true :=
    B.partialTypeAt_fullESocle (ell+1) (insertAddress ell v)
      (by omega) i
  have hBOrdLoop : B.E ell ell = false := by
    change insertE A ell k ell ell = false
    exact insertE_new_loop_false A ell k hk
  have hBNewToOld (i : Fin ell) : B.E ell i.val = false := by
    cases he : B.E ell i.val with
    | false => rfl
    | true =>
      have hlt := (B.E_inside ell i.val he).1
      omega
  have hBToNew (i : Fin ell) :
      B.E i.val ell = decide (i.val < k) := by
    change insertE A ell k (insertAddress ell i.val) ell =
      decide (i.val < k)
    exact insertE_new_column_eq A ell k hell hk i.val
  have hBOld (i j : Fin ell) :
      B.E i.val j.val = A.E i.val j.val := by
    change insertE A ell k (insertAddress ell i.val)
      (insertAddress ell j.val) = A.E i.val j.val
    exact insertE_old_pair_eq A ell k hell hPos i.val j.val
      (lt_of_lt_of_le i.isLt hell)
      (lt_of_lt_of_le j.isLt hell)
  intro x y
  change (B.partialTypeAt (ell+1) (insertAddress ell v)).eRelation x y =
    Q.eRelation x y
  cases x with
  | none =>
    cases y with
    | none => exact hBTypeLoop.trans hQLoop.symm
    | some j => exact (hBRev j).trans (hQRev j).symm
  | some i =>
    cases y with
    | none => exact (hBFull i).trans (hQFull i).symm
    | some j =>
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          change B.E ell ell =
            Q.eRelation (some (Fin.last ell)) (some (Fin.last ell))
          exact hBOrdLoop.trans hQOrdLoop.symm
        | cast j =>
          change B.E ell j.val =
            Q.eRelation (some (Fin.last ell)) (some j.castSucc)
          exact (hBNewToOld j).trans (hValid.newToOldE j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          change B.E i.val ell =
            Q.eRelation (some i.castSucc) (some (Fin.last ell))
          exact (hBToNew i).trans (hValid.oldToNewE i).symm
        | cast j =>
          change B.E i.val j.val =
            Q.eRelation (some i.castSucc) (some j.castSucc)
          exact (hBOld i j).trans (hQOld i j).symm

end SuccessorTree.V10
