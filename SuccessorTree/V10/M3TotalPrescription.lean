import SuccessorTree.V10.M3OutputB2
import SuccessorTree.V10.M3MiddleTarget
import Mathlib.Tactic

/-!
# The total M3 prescribed source function (B1/B2 and admissibility)

Fix n<ell. Every actual admissible level-ell type has a finite
forbidden-free partial-structure witness A,v. Insert the genuine
E3-gated clone of ordinary vertex n at coordinate ell and retain
the complete type of shifted v.

Classical witness selection turns this finite existence into a total
prescription on ALL admissible level-ell source records. Its values
outside that source set are irrelevant to PrescribedBoringData.

The source restriction B1 and admissible output follow from the
actual finite constructor. B2 follows from the independently checked
equality of the COMPLETE ordinary L+ output socle for compatible
source records, including E and absent directed atoms. No global
uniform free cut, no E-age witness and no abstract successor axiom
are introduced.

This is NOT yet global M3: the precise canonical p,c values,
corrected B3 and the duplication conclusion still need connection
to the selected output.
-/

namespace SuccessorTree.V10

/-- Equality of represented raw Kpt nodes identifies their entire
complete L+ records at the same free cut, not just the L reduct. -/
theorem record_eq_of_rawTypeAtFree
    {ell db du dd : Nat}
    (T : PartialTypeWithE ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat)
    (hRaw : (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
      A.rawTypeAtFree v) :
    T = A.partialTypeAt ell v := by
  have hFree : A.freeLevel v = ell := by
    have h := congrArg Sigma.fst hRaw
    change ell = A.freeLevel v at h
    exact h.symm
  have hNode :
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
      (⟨ell,A.partialTypeAt ell v⟩ : RawPartialTypeNode db du dd) := by
    calc
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
          A.rawTypeAtFree v := hRaw
      _ = (⟨ell,A.partialTypeAt ell v⟩ :
          RawPartialTypeNode db du dd) := by
        change (⟨A.freeLevel v,
          A.partialTypeAt (A.freeLevel v) v⟩ :
            RawPartialTypeNode db du dd) = _
        rw [hFree]
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hNode

/-- A chosen finite representative of one admissible level-ell
source record, retaining its actual forbidden-age witness. -/
structure M3ChosenWitness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (T : PartialTypeWithE ell db du dd) where
  A : EnumeratedPartialStructure db du dd
  v : Nat
  hv : v < A.size
  avoids : ∀ bad, bad ∈ family → bad.Avoids A.L
  raw_eq : (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
    A.rawTypeAtFree v

/-- Extract one finite source representative from actual admissibility.
No choice of representative is added to a theorem hypothesis. -/
noncomputable def chooseM3Witness
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    M3ChosenWitness family ell T :=
  Classical.choice (by
    obtain ⟨A,v,hv,hAvoid,hRaw⟩ := hT
    exact ⟨⟨A,v,hv,hAvoid,hRaw⟩⟩)

/-- The selected source vertex has free level ell, and its finite
ambient contains the ell old ordinary vertices. -/
theorem M3ChosenWitness.freeLevel_eq
    {ell db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {T : PartialTypeWithE ell db du dd}
    (W : M3ChosenWitness family ell T) :
    W.A.freeLevel W.v = ell := by
  have hh := congrArg Sigma.fst W.raw_eq
  change ell = W.A.freeLevel W.v at hh
  exact hh.symm

theorem M3ChosenWitness.ell_le_size
    {ell db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {T : PartialTypeWithE ell db du dd}
    (W : M3ChosenWitness family ell T) : ell ≤ W.A.size := by
  have hh := W.freeLevel_eq
  have hCut := W.A.freeLevel_le W.v
  have hv := W.hv
  omega

/-- The exact one-step M3 image obtained from a selected finite
representative; the construction never assigns a new free cut. -/
noncomputable def m3FiniteTarget
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    PartialTypeWithE (ell+1) db du dd :=
  let W := chooseM3Witness family T hT
  (middleCloneInsertPartial W.A ell n W.ell_le_size hn).partialTypeAt
    (ell+1) (insertAddress ell W.v)

/-- The selected finite target is a true extension of the COMPLETE
source L+ type, not only of its relational reduct. -/
theorem m3FiniteTarget_restrict
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    (m3FiniteTarget family n hn T hT).restrict
        (Nat.le_succ ell) = T := by
  let W := chooseM3Witness family T hT
  have hSource : T = W.A.partialTypeAt ell W.v :=
    record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
  change ((middleCloneInsertPartial W.A ell n W.ell_le_size hn).partialTypeAt
    (ell+1) (insertAddress ell W.v)).restrict
      (Nat.le_succ ell) = T
  exact (middleCloneInsertPartial_target_restrict W.A ell n
    W.ell_le_size hn W.v W.hv).trans hSource.symm

/-- The selected finite target is admissible, by actual finite
forbidden-age preservation and transported E free cuts. -/
theorem m3FiniteTarget_admissible
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd)) :
    IsAdmissibleRawType family
      (⟨ell+1,m3FiniteTarget family n hn T hT⟩ :
        RawPartialTypeNode db du dd) := by
  let W := chooseM3Witness family T hT
  change IsAdmissibleRawType family
    (⟨ell+1,
      (middleCloneInsertPartial W.A ell n W.ell_le_size hn).partialTypeAt
        (ell+1) (insertAddress ell W.v)⟩ :
          RawPartialTypeNode db du dd)
  exact middleCloneInsertPartial_target_admissible family W.A
    ell n W.ell_le_size hn W.v W.hv W.freeLevel_eq W.avoids

/-- An arbitrary harmless output used only outside the actual
admissible source set; no statement assumes it is admissible. -/
def m3UnusedTarget (ell db du dd : Nat) :
    PartialTypeWithE (ell+1) db du dd :=
  { lReduct :=
      { binary := fun _ _ _ => false
        unary := fun _ _ => false
        diagonal := fun _ _ => false }
    eRelation := fun _ _ => false }

/-- The genuine total prescribed B1/B2 data for one M3 duplication.
The source set is ALL admissible level-ell types and does not contain
an additional compatibility or canonical successor hypothesis. -/
noncomputable def m3TotalBoringData
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell n : Nat) (hn : n < ell) :
    PrescribedBoringData ell db du dd where
  source := {T | IsAdmissibleRawType family
    (⟨ell,T⟩ : RawPartialTypeNode db du dd)}
  target := fun T => by
    classical
    exact (if hT : IsAdmissibleRawType family
        (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
      m3FiniteTarget family n hn T hT
    else m3UnusedTarget ell db du dd)
  extendsSource := by
    classical
    intro T hT
    change IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) at hT
    change (if hh : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
        m3FiniteTarget family n hn T hh
      else m3UnusedTarget ell db du dd).restrict
        (Nat.le_succ ell) = T
    rw [dif_pos hT]
    exact m3FiniteTarget_restrict family n hn T hT
  preservesCompatibility := by
    classical
    intro T U hT hU hComp
    change IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) at hT
    change IsAdmissibleRawType family
      (⟨ell,U⟩ : RawPartialTypeNode db du dd) at hU
    change SameOrdinarySocle
      (if hh : IsAdmissibleRawType family
        (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
          m3FiniteTarget family n hn T hh
        else m3UnusedTarget ell db du dd)
      (if hh : IsAdmissibleRawType family
        (⟨ell,U⟩ : RawPartialTypeNode db du dd) then
          m3FiniteTarget family n hn U hh
        else m3UnusedTarget ell db du dd)
    rw [dif_pos hT,dif_pos hU]
    let W := chooseM3Witness family T hT
    let V := chooseM3Witness family U hU
    have hWT : T = W.A.partialTypeAt ell W.v :=
      record_eq_of_rawTypeAtFree T W.A W.v W.raw_eq
    have hUV : U = V.A.partialTypeAt ell V.v :=
      record_eq_of_rawTypeAtFree U V.A V.v V.raw_eq
    have hOrd : SameOrdinaryAtCut
        (W.A.partialTypeAt ell W.v)
        (V.A.partialTypeAt ell V.v) := by
      rw [←hWT,←hUV]
      exact hComp
    change SameOrdinarySocle
      ((middleCloneInsertPartial W.A ell n W.ell_le_size hn).partialTypeAt
        (ell+1) (insertAddress ell W.v))
      ((middleCloneInsertPartial V.A ell n V.ell_le_size hn).partialTypeAt
        (ell+1) (insertAddress ell V.v))
    exact middleCloneInsertPartial_sameOrdinarySocle W.A V.A
      ell n W.v V.v W.ell_le_size V.ell_le_size hn hOrd

/-- M3's constructed total prescription has an admissible image
on EVERY prescribed source node; it does not assume this in B3. -/
theorem m3TotalBoringData_target_admissible
    {ell db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (m3TotalBoringData family ell n hn).source) :
    IsAdmissibleRawType family
      (⟨ell+1,(m3TotalBoringData family ell n hn).target T⟩ :
        RawPartialTypeNode db du dd) := by
  classical
  change IsAdmissibleRawType family
    (⟨ell,T⟩ : RawPartialTypeNode db du dd) at hT
  change IsAdmissibleRawType family
    (⟨ell+1,
      if hh : IsAdmissibleRawType family
          (⟨ell,T⟩ : RawPartialTypeNode db du dd) then
        m3FiniteTarget family n hn T hh
      else m3UnusedTarget ell db du dd⟩ :
        RawPartialTypeNode db du dd)
  rw [dif_pos hT]
  exact m3FiniteTarget_admissible family n hn T hT

end SuccessorTree.V10
