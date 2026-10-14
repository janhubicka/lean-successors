import SuccessorTree.V10.I3ClosureSelectedCrossing
import SuccessorTree.V10.KptCompleteSMTree
import SuccessorTree.EnvelopeMinimalityCore
import Mathlib.Tactic

/-!
# Algorithm 5.4 I3 levels: actual selected closure and B3 failure

The generic envelope algorithm's IsInterestingAt predicate is
the disjunction (I1) node, (I2) meet, and (I3) failure of a
one-level skipping map.  On a stage where I1 and I2 both fail,
its remaining third disjunct is precisely the concrete Kpt
NonSkippableClosureCrossing condition.

The preceding file constructs a genuine B1/B2 prescribed
crossing on the actual closure, proves source/target coverage
using absence of (I2), and applies the verified one-gap
extension lemma.  This file performs the final concrete
interface to IsInterestingAt and states the actual I3
signature-count bound.  Its fixed original-name pool must
still be obtained from the maintained stages of the chosen
AlgorithmRun in the global Proposition 6.44 induction.
-/

namespace SuccessorTree.V10

/-- If an Algorithm 5.4 level is interesting but has neither a
closure node nor a closure meet, it is exactly a non-skippable
crossing for the concrete admissible Kpt monoid.  This changes
NO definition of interestingness or the manuscript axioms. -/
theorem algorithmI3_implies_nonSkippableClosureCrossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = ell)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell)
    (hInteresting :
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Z ell) :
    NonSkippableClosureCrossing family Z ell := by
  have hNoMMap :
      ¬ ∃ D : SuccessorTree.MMap (normalizedKptSMTree family),
        D.map.SkipsOnly ell ∧
        ∀ z : AdmissibleKptNode family, z ∈ Z →
          ∀ (hz : ell < LevelTree.lev z),
            D (LevelTree.ancestor z ell (Nat.le_of_lt hz)) =
              LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz) := by
    rcases hInteresting with hNode | hOther
    · exact False.elim (hNoI1 hNode)
    · rcases hOther with hMeet | hI3
      · exact False.elim (hNoI2 hMeet)
      · exact hI3
  intro hPossible
  obtain ⟨Φ,hMem,hSkip,hAgree⟩ := hPossible
  let D : SuccessorTree.MMap (normalizedKptSMTree family) :=
    ⟨Φ,hMem⟩
  apply hNoMMap
  refine ⟨D,hSkip,?_⟩
  intro z hz hzCut
  exact hAgree z hz hzCut

/-- In the actual normalized Kpt tree, an interesting positive
stage whose node and meet events fail has a genuine finite
L-only corrected-B3 failure for the canonical selected
closure-crossing map.  This is precisely the B3 reduction
used immediately before Observation 6.52 in the manuscript. -/
theorem algorithmI3_failsCorrectedB3
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Set (AdmissibleKptNode family))
    (hPool : ∀ z, z ∈ Z →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (ell : Nat) (hPos : 0 < ell)
    (hNoI1 : ¬ ∃ z : AdmissibleKptNode family,
      z ∈ Z ∧ LevelTree.lev z = ell)
    (hNoI2 : ¬ ∃ a : AdmissibleKptNode family,
      a ∈ Z ∧ ∃ b : AdmissibleKptNode family,
        b ∈ Z ∧ SMTree.Envelope.SameComponent a b ∧
        LevelTree.lev (LevelTree.meet a b) = ell)
    (hInteresting :
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) Z ell) :
    ¬ (closureSelectedBoringData family A hAvoid original Z ell).CorrectedB3
      family := by
  have hNoSkip := algorithmI3_implies_nonSkippableClosureCrossing
    family Z ell hNoI1 hNoI2 hInteresting
  exact closureSelectedBoringData_failedB3_of_nonSkippable
    family A hAvoid original Z hPool ell hPos hNoI2 hNoSkip

/-- Observation 6.52 for the ACTUAL positive I3 stages of the
normalized Algorithm 5.4, without independent assumptions of
failed B3 tests, selected sources, forbidden age witnesses or
injective signature codes.

A single FIXED set of M original names must represent all the
closure stages under comparison.  Restricting that pool to
higher-generation names will give the R(M_r) bound in the full
downward induction. -/
theorem algorithmI3Levels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (original : Fin M → Fin A.size)
    (Z : Nat → Set (AdmissibleKptNode family))
    (levels : Finset Nat)
    (hLevel : ∀ ell, ell ∈ levels →
      0 < ell ∧ ell < A.size)
    (hPool : ∀ ell, ell ∈ levels → ∀ z, z ∈ Z ell →
      ∃ v : Fin M, z ≤ A.kptOriginal family hAvoid (original v))
    (hNoI1 : ∀ ell, ell ∈ levels →
      ¬ ∃ z : AdmissibleKptNode family,
        z ∈ Z ell ∧ LevelTree.lev z = ell)
    (hNoI2 : ∀ ell, ell ∈ levels →
      ¬ ∃ a : AdmissibleKptNode family,
        a ∈ Z ell ∧ ∃ b : AdmissibleKptNode family,
          b ∈ Z ell ∧ SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = ell)
    (hInteresting : ∀ ell, ell ∈ levels →
      SMTree.Envelope.IsInterestingAt
        (normalizedKptSMTree family) (Z ell) ell) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M := by
  apply representedNonSkippableLevels_card_le_signature_capacity
    family A hAvoid original Z levels hLevel hPool hNoI2
  intro ell hEll
  exact algorithmI3_implies_nonSkippableClosureCrossing
    family (Z ell) ell (hNoI1 ell hEll) (hNoI2 ell hEll)
    (hInteresting ell hEll)

end SuccessorTree.V10
