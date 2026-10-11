import SuccessorTree.V10.PrescribedImageRepresentation
import SuccessorTree.V10.LocalAgeNeutralPrefix
import Mathlib.Tactic

/-!
# Prefix coherence of the genuine prescribed insertion

These statements isolate the parts of predecessor preservation that do
not require the global choice construction. In particular, the matching
decision is constant on comparable types above the insertion level,
and the finite inserted full L+ record commutes with the one-filler
prefix replica. Strictly below the gap, all retained records are unchanged.

The total-map predecessor theorem is deliberately not asserted here.
-/

namespace SuccessorTree.V10

/-- Above the gap, comparable nodes have *identical* complete ell-prefixes.
In particular, the prescribed/neutral decision cannot change as the
ordinary cutoff grows. No B3 or admissibility-of-target hypothesis is used. -/
theorem PrescribedBoringData.compatibleSource_iff_of_prefix
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    {family : List (NormalizedForbidden db du dd)}
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a) (hlevB : ell ≤ b.1.1) :
    F.HasCompatibleSource (b.1.2.restrict hlevB) ↔
      F.HasCompatibleSource
        (a.1.2.restrict (hlevB.trans (show b.1.1 ≤ a.1.1 from hba.1))) := by
  have hPrefix : b.1.2 =
      a.1.2.restrict (show b.1.1 ≤ a.1.1 from hba.1) := hba.2
  have hSame : b.1.2.restrict hlevB =
      a.1.2.restrict (hlevB.trans (show b.1.1 ≤ a.1.1 from hba.1)) := by
    rw [hPrefix, PartialTypeWithE.restrict_trans]
  rw [hSame]

/-- Full-record replica comparison for a prescribed column at a single
cut. The two finite structures may have different distinguished-vertex
indices; their inserted ordinary E cuts are the *same actual* canonical
cut here. No forbidden-age or abstract prefix assumption is needed. -/
theorem PrescribedBoringData.prescribedInsert_prefixReplica_type_eq
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (k : Nat) (hValid : ValidNewOrdinaryColumn Q k)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (v cut : Nat) (hv : v < A.size)
    (hd : cut ≤ A.freeLevel v)
    (hPos : 0 < ell) (hEll : ell ≤ cut) :
    let R := prefixReplicaPartialStructure A v cut hv hd
    (prescribedInsertPartial A Q k hValid (by
        have h := A.freeLevel_le v
        omega) hPos hk hGate
      (F.upperIncoming A) (F.upperOutgoing A)).partialTypeAt
        (cut+1) (insertAddress ell v) =
    (prescribedInsertPartial R Q k hValid (by
        change ell ≤ cut+2
        omega) hPos hk hGate
      (F.upperIncoming R) (F.upperOutgoing R)).partialTypeAt
        (cut+1) (insertAddress ell (cut+1)) := by
  let R := prefixReplicaPartialStructure A v cut hv hd
  have hcutA : cut ≤ A.size := by
    have h := A.freeLevel_le v
    omega
  have hcutR : cut ≤ R.size := by
    change cut ≤ cut+2
    omega
  have hvCut : cut ≤ v := hd.trans (A.freeLevel_le v)
  have hwCut : cut ≤ cut+1 := by omega
  have hvR : cut+1 < R.size := by
    change cut+1 < cut+2
    omega
  have hSource : A.partialTypeAt cut v = R.partialTypeAt cut (cut+1) :=
    (prefixReplicaPartialStructure_type_eq A v cut hv hd).symm
  exact F.prescribedInsertPartial_independent A R Q Q k k
    hValid hValid (sameOrdinarySocle_refl Q) hk hk hGate hGate
    cut v (cut+1) hPos hEll hcutA hcutR hvCut hwCut hv hvR hSource

/-- No new coordinate enters a record at or below ell, even when the
inserted ordinary column is non-neutral. This includes all E atoms,
both directions of L atoms, absent relations, unary and diagonal data. -/
theorem prescribedInsertPartial_type_below_gap
    {ell db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (k : Nat) (hValid : ValidNewOrdinaryColumn Q k)
    (hell : ell ≤ A.size) (hPos : 0 < ell)
    (hk : k ≤ ell) (hGate : k = 0 ∨ k < ell)
    (upperIncoming upperOutgoing : Nat → Fin db → Bool)
    (v cut : Nat) (hv : v < A.size) (hLow : cut ≤ ell) :
    (prescribedInsertPartial A Q k hValid hell hPos hk hGate
      upperIncoming upperOutgoing).partialTypeAt cut
        (insertAddress ell v) = A.partialTypeAt cut v := by
  let B := prescribedInsertPartial A Q k hValid hell hPos hk hGate
    upperIncoming upperOutgoing
  have hIns := prescribedInsertPartial_isLInsertion A Q k hValid
    hell hPos hk hGate upperIncoming upperOutgoing
  have hCut : cut ≤ A.size := hLow.trans hell
  have hCoord : ∀ a : Option (Fin cut),
      prefixVertexIndex (insertAddress ell v) a =
        insertAddress ell (prefixVertexIndex v a) := by
    intro a
    cases a with
    | none => rfl
    | some a =>
        change a.val = insertAddress ell a.val
        exact (insertAddress_below ell a.val
          (lt_of_lt_of_le a.isLt hLow)).symm
  have hIn : ∀ a : Option (Fin cut), prefixVertexIndex v a < A.size :=
    fun a => prefixVertexIndex_inside v A.size hv hCut a
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro a b r
      change B.L.binary
          (prefixVertexIndex (insertAddress ell v) a)
          (prefixVertexIndex (insertAddress ell v) b) r =
        A.L.binary (prefixVertexIndex v a) (prefixVertexIndex v b) r
      rw [hCoord a, hCoord b]
      exact hIns.binary _ _ (hIn a) (hIn b) r
    · intro a r
      change B.L.unary (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.unary (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.unary _ (hIn a) r
    · intro a r
      change B.L.diagonal (prefixVertexIndex (insertAddress ell v) a) r =
        A.L.diagonal (prefixVertexIndex v a) r
      rw [hCoord a]
      exact hIns.diagonal _ (hIn a) r
  · intro a b
    change B.E (prefixVertexIndex (insertAddress ell v) a)
        (prefixVertexIndex (insertAddress ell v) b) =
      A.E (prefixVertexIndex v a) (prefixVertexIndex v b)
    rw [hCoord a, hCoord b]
    exact insertE_old_pair_eq A ell k hell hPos
      _ _ (hIn a) (hIn b)

end SuccessorTree.V10
