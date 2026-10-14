import SuccessorTree.V10.I3ActualGraphRepresentation
import SuccessorTree.V10.ConcreteOriginalPool
import Mathlib.Tactic

/-!
# Section 6: from represented closure crossings to original names

Algorithm 5.4's actual f_ell sends the old ancestor at ell
of a closure node z to its next ancestor at ell+1.  Once (I2)
has ruled out competing next ancestors this is a partial function.

The concrete original-pool invariant says every z in that
closure is below an original in the maintained pool.  Therefore
BOTH ancestors of z are the complete partial types of the SAME
ambient original, provided z lies strictly above ell.  This
is the manuscript's source-to-original graph representation,
not an abstract extra axiom about age witnesses.

This file isolates the exact transfer.  It does not yet prove
that Algorithm 5.4's actual f_ell has the displayed graph:
that is the remaining one-step closure/no-(I2) identification.
The age witness stays purely in L.
-/

namespace SuccessorTree.V10

/-- A source/target pair of a prescribed crossing is witnessed by
the consecutive ancestors of one closure node.  The identity uses
WHOLE raw partial types, not merely their L reducts, so E and
negative relation bits are retained automatically. -/
def IsCrossingGraphOf
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat)
    (F : PrescribedBoringData ell db du dd) : Prop :=
  ∀ T, T ∈ F.source →
    ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧
      ∃ (hz : ell < LevelTree.lev z),
        (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
          (LevelTree.ancestor z ell (Nat.le_of_lt hz)).val ∧
        (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) =
          (LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)).val

/-- A real source/target crossing over a closure represented by a
FIXED finite pool has one SAME ambient original for its complete
old and new type, with the necessary free-cut guard.
The only hypotheses are precisely the geometric closure
representation and the actual crossing graph. -/
theorem crossingGraph_source_has_ambient_original
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (ell : Nat)
    (F : PrescribedBoringData ell db du dd)
    (hGraph : IsCrossingGraphOf family Z ell F) :
    ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        ell+1 ≤ A.freeLevel (original v).val ∧
        T = A.partialTypeAt ell (original v).val ∧
        F.target T = A.partialTypeAt (ell+1) (original v).val := by
  intro T hT
  obtain ⟨z,hZ,hz,hOld,hNew⟩ := hGraph T hT
  obtain ⟨v,hZv⟩ := hPool z hZ
  have hLv : LevelTree.lev z ≤ A.freeLevel (original v).val := by
    have h := LevelTree.level_le_of_le hZv
    change LevelTree.lev z ≤ A.freeLevel (original v).val at h
    exact h
  have hCut : ell+1 ≤ A.freeLevel (original v).val := by omega
  have hOldBelow :
      LevelTree.ancestor z ell (Nat.le_of_lt hz) ≤
        A.kptOriginal family hAvoid (original v) :=
    (LevelTree.ancestor_le z ell (Nat.le_of_lt hz)).trans hZv
  have hNewBelow :
      LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz) ≤
        A.kptOriginal family hAvoid (original v) :=
    (LevelTree.ancestor_le z (ell+1) (Nat.succ_le_iff.mpr hz)).trans hZv
  have hOldRaw :=
    kpt_prefix_raw_eq_ambient A family hAvoid (original v)
      (LevelTree.ancestor z ell (Nat.le_of_lt hz)) hOldBelow
  have hNewRaw :=
    kpt_prefix_raw_eq_ambient A family hAvoid (original v)
      (LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)) hNewBelow
  have hOldLevel :
      LevelTree.lev (LevelTree.ancestor z ell (Nat.le_of_lt hz)) = ell :=
    LevelTree.level_ancestor z ell (Nat.le_of_lt hz)
  have hNewLevel :
      LevelTree.lev
        (LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)) = ell+1 :=
    LevelTree.level_ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)
  rw [hOldLevel] at hOldRaw
  rw [hNewLevel] at hNewRaw
  have hOldPair :
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
        (⟨ell,A.partialTypeAt ell (original v).val⟩ :
          RawPartialTypeNode db du dd) :=
    hOld.trans hOldRaw
  have hNewPair :
      (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) =
        (⟨ell+1,A.partialTypeAt (ell+1) (original v).val⟩ :
          RawPartialTypeNode db du dd) :=
    hNew.trans hNewRaw
  have hOldType :
      T = A.partialTypeAt ell (original v).val := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hOldPair
  have hNewType :
      F.target T = A.partialTypeAt (ell+1) (original v).val := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hNewPair
  exact ⟨v,hCut,hOldType,hNewType⟩

/-- Observation 6.52: once each genuinely selected closure-stage
crossing has the graph above and its closure is represented by the
same fixed finite original pool, all failed selected levels have
the paper's R(M) bound.  No additional selected predicate or
signature-injectivity hypothesis remains. -/
theorem crossingGraph_failed_levels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Nat → Set (AdmissibleKptNode family))
    (F : (ell : Nat) → PrescribedBoringData ell db du dd)
    (levels : Finset Nat)
    (hFailed : ∀ ell, ell ∈ levels →
      ell < A.size ∧ ¬ (F ell).CorrectedB3 family)
    (hPool : ∀ ell, ell ∈ levels → ∀ z, z ∈ Z ell →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (hGraph : ∀ ell, ell ∈ levels →
      IsCrossingGraphOf family (Z ell) ell (F ell)) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M := by
  apply actualRepresentedI3_failure_levels_card_le_signature_capacity
    family A original F levels hFailed
  intro ell hEll
  exact crossingGraph_source_has_ambient_original
    family A hAvoid original (Z ell)
    (hPool ell hEll) ell (F ell) (hGraph ell hEll)

end SuccessorTree.V10
