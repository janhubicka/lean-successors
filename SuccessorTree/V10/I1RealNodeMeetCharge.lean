import SuccessorTree.V10.KptStageClosureNormalForm
import SuccessorTree.V10.HPositiveFreeLevelOdd
import SuccessorTree.V10.HGenerationHighBudget
import Mathlib.Tactic

/-!
# Proposition 6.44: real I1 events are charged original-pair meets

The complete Kpt closure normal form is seed / selected parameter /
meet of original types. The exact finite H free-cut theorem says
every selected parameter with a positive free cut has ODD level,
whereas a real H coordinate iota(p,r) is EVEN.

Thus a closure node at an intermediate real positive-generation
level can arise by (I1) only as an original-pair meet, provided
the actual INITIAL SEEDS do not already have this level. This
last condition is true for the manuscript's chosen top-generation
seeds and their displayed fake/end prefixes, but its concrete
construction still needs to be connected to the Lean application.

The second theorem checks that such a meet is nontrivial:
it cannot equal either full original type because positive
original free cuts are odd. Applying the already-verified H
relational meet theorem gives the EXACT NumericHMeetCharge,
which the common higher-original budget bounds linearly.
-/

namespace SuccessorTree.V10

/-- Under the genuine numerical H parity, (I1) at a real
intermediate positive-generation level is already the meet
of two ambient original types in the maintained finite pool,
unless that level belongs to one of the explicitly supplied
initial seed nodes. -/
theorem numericH_real_I1_node_is_original_meet
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U : Set (Fin N))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) U)
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X)
    (p r : Nat)
    (hLevel : LevelTree.lev z = hPosition k p r)
    (hNoSeed : ∀ x, x ∈ X →
      LevelTree.lev x ≠ hPosition k p r) :
    ∃ v : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      ∃ w : Fin N,
        w ∈ ambientStagePool (finiteNumericH K k N) U I ∧
        SMTree.Envelope.SameComponent
          ((finiteNumericH K k N).kptOriginal family
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) v)
          ((finiteNumericH K k N).kptOriginal family
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) w) ∧
        z = LevelTree.meet
          ((finiteNumericH K k N).kptOriginal family
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) v)
          ((finiteNumericH K k N).kptOriginal family
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) w) := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  have hNotSeed : z ∉ X := by
    intro hZ
    exact (hNoSeed z hZ) hLevel
  have hNotParam : ¬ ∃ i : Fin A.size,
      i.val ∈ I ∧ 0 < A.freeLevel i.val ∧
      z = A.kptOriginal family hAvoidA i := by
    rintro ⟨i,_hi,hFree,hEq⟩
    have hParamLevel : LevelTree.lev z = A.freeLevel i.val := by
      rw [hEq]
      rfl
    have hFreeEq : A.freeLevel i.val = hPosition k p r :=
      hParamLevel.symm.trans hLevel
    exact (finiteNumericH_positive_freeLevel_ne_realPosition
      K k N i.val p r i.isLt hFree) hFreeEq
  exact admissibleKpt_actual_closure_node_original_meet
    family A hAvoidA I X U hX z hz hNotSeed hNotParam

/-- Every such (I1) real node is not merely equal to some
original-pair meet: its meeting originals are strictly above
the meet, so the exact H numerical charge applies. No new
meet-projection or generation hypothesis is assumed. -/
theorem numericH_real_I1_node_has_higher_original_charge
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U : Set (Fin N))
    (hX : X ⊆ ambientPrefixPool family
      (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK) U)
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X)
    (p r : Nat) (hr : 0 < r) (hrk : r ≤ k)
    (hLevel : LevelTree.lev z = hPosition k p r)
    (hNoSeed : ∀ x, x ∈ X →
      LevelTree.lev x ≠ hPosition k p r) :
    ∃ v w : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      w ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      NumericHMeetCharge K.binary k v.val w.val p r := by
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  obtain ⟨v,hv,w,hw,hCommon,hMeet⟩ :=
    numericH_real_I1_node_is_original_meet
      family K hCarrier hAvoidK k N I X U hX z hz p r
      hLevel hNoSeed
  let ov : AdmissibleKptNode family := A.kptOriginal family hAvoidA v
  let ow : AdmissibleKptNode family := A.kptOriginal family hAvoidA w
  have hMeetLevel :
      LevelTree.lev (LevelTree.meet ov ow) = hPosition k p r := by
    rw [←hMeet]
    exact hLevel
  have hLevelPos : 0 < hPosition k p r := by
    unfold hPosition
    omega
  have hNotLeft : LevelTree.meet ov ow ≠ ov := by
    intro hEq
    have hF : A.freeLevel v.val = hPosition k p r := by
      have hLevOriginal : LevelTree.lev ov = A.freeLevel v.val := rfl
      calc
        A.freeLevel v.val = LevelTree.lev ov := hLevOriginal.symm
        _ = LevelTree.lev (LevelTree.meet ov ow) := by rw [hEq]
        _ = hPosition k p r := hMeetLevel
    have hPositive : 0 < A.freeLevel v.val := by omega
    exact (finiteNumericH_positive_freeLevel_ne_realPosition
      K k N v.val p r v.isLt hPositive) hF
  have hNotRight : LevelTree.meet ov ow ≠ ow := by
    intro hEq
    have hF : A.freeLevel w.val = hPosition k p r := by
      have hLevOriginal : LevelTree.lev ow = A.freeLevel w.val := rfl
      calc
        A.freeLevel w.val = LevelTree.lev ow := hLevOriginal.symm
        _ = LevelTree.lev (LevelTree.meet ov ow) := by rw [hEq]
        _ = hPosition k p r := hMeetLevel
    have hPositive : 0 < A.freeLevel w.val := by omega
    exact (finiteNumericH_positive_freeLevel_ne_realPosition
      K k N w.val p r w.isLt hPositive) hF
  have hCharge : NumericHMeetCharge K.binary k v.val w.val p r :=
    finiteNumericH_prefix_meet_charge
      family K k N hk hAvoidA
      v.val w.val v.isLt w.isLt ov ow
      le_rfl le_rfl hCommon hNotLeft hNotRight
      p r hr hrk hMeetLevel
  exact ⟨v,w,hv,hw,hCharge⟩

end SuccessorTree.V10
