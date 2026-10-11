import SuccessorTree.V10.LocalAgeNeutralImageUnique
import Mathlib.Tactic

/-!
# Neutral insertion respects genuine Kpt prefixes above the inserted level

For a pair b<=a of admissible Kpt types, both of levels at least ell>0,
we may represent the larger type in a forbidden-free ambient A and form
the single-neutral-filler prefix replica of its shorter prefix. The replica
realizes exactly the complete source type b at its free cut.

The established representation-independence theorem shows that neutral
insertion of this prefix replica has the same complete type as the neutral
insertion of A restricted to the corresponding shifted cut. This yields
a literal Kpt prefix relation, with the full E and L records unchanged.

No arbitrary abstract prefix-copying interface is assumed. This theorem
controls the ABOVE-GAP part of a candidate global shape map; crossing the
gap and preserving the successor decomposition are next.
-/

namespace SuccessorTree.V10

/-- Exact agreement between the neutral insertion of an original type
at a shorter cut and the neutral insertion of its one-filler prefix
replica. This is equality of the COMPLETE new L+ type. -/
theorem neutralInsert_prefixReplica_type_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v d ell : Nat) (hv : v < A.size)
    (hd : d ≤ A.freeLevel v)
    (hellPos : 0 < ell) (hellD : ell ≤ d) :
    let R := prefixReplicaPartialStructure A v d hv hd
    (neutralInsert A ell (by
        have h := A.freeLevel_le v
        omega) hellPos).partialTypeAt
        (d + 1) (insertAddress ell v) =
      (neutralInsert R ell (by
        change ell ≤ d + 2
        omega) hellPos).partialTypeAt
        (d + 1) (insertAddress ell (d + 1)) := by
  let R := prefixReplicaPartialStructure A v d hv hd
  have hellA : ell ≤ A.size := by
    have h := A.freeLevel_le v
    omega
  have hellR : ell ≤ R.size := by
    change ell ≤ d + 2
    omega
  have hCutA : d ≤ A.size := by
    have h := A.freeLevel_le v
    omega
  have hCutR : d ≤ R.size := by
    change d ≤ d+2
    omega
  have hvR : d + 1 < R.size := by
    change d+1 < d+2
    omega
  have hSource : A.partialTypeAt d v = R.partialTypeAt d (d+1) :=
    (prefixReplicaPartialStructure_type_eq A v d hv hd).symm
  exact neutralInsert_partialType_independent A R ell d v (d+1)
    hellA hellR hellPos hellD hCutA hCutR hv hvR hSource

/-- The actually CHOSEN normalized admissible neutral images of two
prefix-comparable nodes remain prefix-comparable above the gap.
No representation choice survives in the theorem statement. -/
theorem neutralKptImage_prefix_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    (a b : AdmissibleKptNode family)
    (hba : b ≤ a)
    (hlevB : ell ≤ b.1.1) :
    neutralKptImage family ell hellPos b hlevB ≤
      neutralKptImage family ell hellPos a
        (by
          have hraw : b.1 ≤ a.1 := hba
          exact hlevB.trans hraw.1) := by
  have hRawBA : b.1 ≤ a.1 := hba
  let d : Nat := b.1.1
  have hda : d ≤ a.1.1 := hRawBA.1
  have hlevA : ell ≤ a.1.1 := hlevB.trans hda
  obtain ⟨A, v, hellA, hv, hAvoidA, hRawA, hImgA⟩ :=
    neutralKptImage_isImage family ell hellPos a hlevA
  have hSourceLev : a.1.1 = A.freeLevel v :=
    congrArg Sigma.fst hRawA
  have hd : d ≤ A.freeLevel v := by omega
  have hEllD : ell ≤ d := hlevB
  let R := prefixReplicaPartialStructure A v d hv hd
  have hRFree : R.freeLevel (d+1) = d :=
    prefixReplicaPartialStructure_freeLevel A v d hv hd
  have hvR : d+1 < R.size := by
    change d+1 < d+2
    omega
  have hellR : ell ≤ R.size := by
    change ell ≤ d+2
    omega
  have hAvoidR : ∀ bad, bad ∈ family → bad.Avoids R.L := by
    intro bad hbad
    exact bad.replica_preserves_avoidance A v d hv hd (hAvoidA bad hbad)
  have hSigmaA :
      (⟨a.1.1, a.1.2⟩ : RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ :
        RawPartialTypeNode db du dd) := hRawA
  have hRawHEq :
      HEq a.1.2 (A.partialTypeAt (A.freeLevel v) v) :=
    (Sigma.mk.inj_iff.mp hSigmaA).2
  have hValA : a.1.2 = A.partialTypeAt a.1.1 v := by
    rw [← hSourceLev] at hRawHEq
    exact eq_of_heq hRawHEq
  have hRawBType : b.1.2 = A.partialTypeAt d v := by
    calc
      b.1.2 = a.1.2.restrict hda := hRawBA.2
      _ = (A.partialTypeAt a.1.1 v).restrict hda := by rw [hValA]
      _ = A.partialTypeAt d v :=
        A.partialTypeAt_restrict d a.1.1 v hda
  have hRawB : b.1 =
      (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) := by
    calc
      b.1 = (⟨d, b.1.2⟩ : RawPartialTypeNode db du dd) :=
        (Sigma.eta b.1).symm
      _ = (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) :=
        congrArg (Sigma.mk d) hRawBType
  have hReplicaRaw : R.rawTypeAtFree (d+1) =
      (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) := by
    change
      (⟨R.freeLevel (d+1),
         R.partialTypeAt (R.freeLevel (d+1)) (d+1)⟩ :
        RawPartialTypeNode db du dd) =
      (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd)
    rw [hRFree]
    exact congrArg (Sigma.mk d)
      (prefixReplicaPartialStructure_type_eq A v d hv hd)
  have hRepB : b.1 = R.rawTypeAtFree (d+1) :=
    hRawB.trans hReplicaRaw.symm
  have hImgB :
      (neutralKptImage family ell hellPos b hlevB).1 =
        (neutralInsert R ell hellR hellPos).rawTypeAtFree
          (insertAddress ell (d+1)) :=
    neutralKptImage_eq_of_representation family ell hellPos b hlevB
      R (d+1) hvR hAvoidR hRepB hellR
  let B := neutralInsert A ell hellA hellPos
  let Q := neutralInsert R ell hellR hellPos
  have hcutA : ell ≤ A.freeLevel v := by omega
  have hcutR : ell ≤ R.freeLevel (d+1) := by omega
  have hFreeA : B.freeLevel (insertAddress ell v) =
      A.freeLevel v + 1 := by
    have h := neutralInsert_freeLevel_old A ell hellA hellPos v hv
    simpa only [B, if_neg (Nat.not_lt.mpr hcutA)] using h
  have hFreeR : Q.freeLevel (insertAddress ell (d+1)) = d+1 := by
    have h := neutralInsert_freeLevel_old R ell hellR hellPos (d+1) hvR
    rw [if_neg (Nat.not_lt.mpr hcutR), hRFree] at h
    exact h
  have hType : B.partialTypeAt (d+1) (insertAddress ell v) =
      Q.partialTypeAt (d+1) (insertAddress ell (d+1)) :=
    neutralInsert_prefixReplica_type_eq A v d ell hv hd hellPos hEllD
  have hRawQ :
      Q.rawTypeAtFree (insertAddress ell (d+1)) =
      (⟨d+1, B.partialTypeAt (d+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd) := by
    change
      (⟨Q.freeLevel (insertAddress ell (d+1)),
         Q.partialTypeAt (Q.freeLevel (insertAddress ell (d+1)))
           (insertAddress ell (d+1))⟩ : RawPartialTypeNode db du dd) =
      (⟨d+1, B.partialTypeAt (d+1) (insertAddress ell v)⟩ :
        RawPartialTypeNode db du dd)
    rw [hFreeR]
    exact congrArg (Sigma.mk (d+1)) hType.symm
  have hbound : d+1 ≤ B.freeLevel (insertAddress ell v) := by
    rw [hFreeA]
    omega
  have hPrefix :
      Q.rawTypeAtFree (insertAddress ell (d+1)) ≤
        B.rawTypeAtFree (insertAddress ell v) := by
    rw [hRawQ]
    exact rawPartialType_prefix_of_cut B (insertAddress ell v) (d+1) hbound
  change
    (neutralKptImage family ell hellPos b hlevB).1 ≤
      (neutralKptImage family ell hellPos a hlevA).1
  rw [hImgB, hImgA]
  exact hPrefix

end SuccessorTree.V10
