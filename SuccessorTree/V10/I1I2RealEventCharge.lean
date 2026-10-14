import SuccessorTree.V10.HTopGenerationSeeds
import SuccessorTree.V10.HClosureCharge
import Mathlib.Tactic

/-!
# Proposition 6.44: both I1 and I2 real events carry an actual H meet charge

For the manuscript's finite top-generation seed family, a selected
closure node at an intermediate real generation already has an
original-pair meet charge (the checked I1 normal-form route).

An (I2) meet can be trivial, equal to either operand. In that
case the corresponding operand itself satisfies I1, and the
same charge theorem applies. Otherwise the meet is strict in
both operands, and the concrete closure meet-charge theorem
provides a positive-generation original of strictly higher
generation with its unique first-neighbour charge.

This resolves the EVENT-CLASSIFICATION step at one stage of
Algorithm 5.4. The additional cardinal passage to M_r uses
the stage-to-final-pool inclusion and the already checked
hGenerationHighOriginals budget.
-/

namespace SuccessorTree.V10

/-- At an intermediate real numerical H coordinate, either
an I1 node or an I2 meet in the ACTUAL Kpt closure has the
same original-pair charge. Trivial I2 meets are reduced to I1,
not incorrectly submitted to a nontrivial-meet lemma. -/
theorem numericHTopSeeds_real_I1I2_has_charge
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (I : Set Nat)
    (p r : Nat) (hr : 0 < r) (hrk : r < k)
    (hEvent :
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) I
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        LevelTree.lev z = hPosition k p r) ∨
      (∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure
          (admissibleKptSTree family) I
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure
            (admissibleKptSTree family) I
            (numericHTopGenerationSeeds family K k N
              (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
              c blocks hWithin) ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = hPosition k p r)) :
    ∃ v w : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N)
        ({c} : Set (Fin N)) I ∧
      w ∈ ambientStagePool (finiteNumericH K k N)
        ({c} : Set (Fin N)) I ∧
      NumericHMeetCharge K.binary k v.val w.val p r := by
  let hAvoidH :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X := numericHTopGenerationSeeds family K k N hAvoidH c blocks hWithin
  have hX : (X : Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family (finiteNumericH K k N)
        hAvoidH ({c} : Set (Fin N)) :=
    numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoidH c blocks hWithin
  rcases hEvent with ⟨z,hz,hLevel⟩ | ⟨a,ha,b,hb,hSame,hLevel⟩
  · exact numericHTopSeeds_realI1_meet_charge
      family K hCarrier hAvoidK k N hk c blocks hWithin I
      z hz p r hr hrk hLevel
  · by_cases hLeft : LevelTree.meet a b = a
    · have haLevel : LevelTree.lev a = hPosition k p r := by
        rw [←hLeft]
        exact hLevel
      exact numericHTopSeeds_realI1_meet_charge
        family K hCarrier hAvoidK k N hk c blocks hWithin I
        a ha p r hr hrk haLevel
    · by_cases hRight : LevelTree.meet a b = b
      · have hbLevel : LevelTree.lev b = hPosition k p r := by
          rw [←hRight]
          exact hLevel
        exact numericHTopSeeds_realI1_meet_charge
          family K hCarrier hAvoidK k N hk c blocks hWithin I
          b hb p r hr hrk hbLevel
      · exact forbiddenFreeH_closure_meet_charge
          family K hCarrier k N hk hAvoidK
          ({c} : Set (Fin N)) I X hX
          a b ha hb hSame hLeft hRight p r hr
          (Nat.le_of_lt hrk) hLevel

end SuccessorTree.V10
