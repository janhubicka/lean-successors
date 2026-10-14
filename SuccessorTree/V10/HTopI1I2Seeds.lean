import SuccessorTree.V10.HTopGenerationExclusions
import SuccessorTree.V10.HTopGenerationSeeds
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: top-generation I1/I2 events are initial seeds

The q+1 seed cardinality bound is not enough by itself.
One must also rule out new top-generation closure nodes.
The actual closure normal form says every node is a seed,
a selected Kpt parameter, or a meet of two ambient originals.

At a real top-generation position iota(p,k), a selected
parameter is impossible by odd positive E-free cut parity.
A nontrivial meet of original types is impossible because
the numerical meet charge would require generation >k.
A trivial meet is a full original, also excluded by parity.
Therefore any I1 top-generation node is an initial seed.

For an I2 event, a trivial meet reduces to I1; a strict
meet is impossible by the separate checked top-generation
closure-meet exclusion. Hence every I1/I2 event at real
generation k is already represented among the q+1 seeds.

The remaining top-stage I3 exclusion is supplied by the
top B3 theorem, once its actual AlgorithmRun source is
identified. No new language or axioms are introduced here.
-/

namespace SuccessorTree.V10

/-- At a real H top-generation coordinate, any actual Kpt
closure node must be an INITIAL top-generation seed. -/
theorem numericHTopSeeds_real_top_I1_is_seed
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
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin))
    (p : Nat)
    (hLevel : LevelTree.lev z = hPosition k p k) :
    z ∈ numericHTopGenerationSeeds family K k N
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin := by
  classical
  let A : EnumeratedPartialStructure db du dd := finiteNumericH K k N
  let hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    finiteNumericH_avoids_family family K hCarrier k N hAvoidK
  let X : Set (AdmissibleKptNode family) :=
    numericHTopGenerationSeeds family K k N hAvoidA c blocks hWithin
  have hX : X ⊆ ambientPrefixPool family A hAvoidA
      ({c} : Set (Fin N)) :=
    numericHTopGenerationSeeds_subset_rootPool
      family K k N hAvoidA c blocks hWithin
  by_contra hNotSeed
  have hNotParam : ¬ ∃ i : Fin A.size,
      i.val ∈ I ∧ 0 < A.freeLevel i.val ∧
      z = A.kptOriginal family hAvoidA i := by
    rintro ⟨i,_hi,hFree,hEq⟩
    have hAt : A.freeLevel i.val = hPosition k p k := by
      have hLev : LevelTree.lev z = A.freeLevel i.val := by
        rw [hEq]
        rfl
      exact hLev.symm.trans hLevel
    exact (finiteNumericH_positive_freeLevel_ne_realPosition
      K k N i.val p k i.isLt hFree) hAt
  obtain ⟨v,_hv,w,_hw,hCommon,hMeet⟩ :=
    admissibleKpt_actual_closure_node_original_meet
      family A hAvoidA I X ({c} : Set (Fin N)) hX
      z hz hNotSeed hNotParam
  let ov : AdmissibleKptNode family :=
    A.kptOriginal family hAvoidA v
  let ow : AdmissibleKptNode family :=
    A.kptOriginal family hAvoidA w
  have hMeetLevel :
      LevelTree.lev (LevelTree.meet ov ow) = hPosition k p k := by
    rw [←hMeet]
    exact hLevel
  have hRealPos : 0 < hPosition k p k := by
    unfold hPosition
    omega
  have hNotLeft : LevelTree.meet ov ow ≠ ov := by
    intro heq
    have hf : A.freeLevel v.val = hPosition k p k := by
      calc
        A.freeLevel v.val = LevelTree.lev ov := rfl
        _ = LevelTree.lev (LevelTree.meet ov ow) := by rw [heq]
        _ = hPosition k p k := hMeetLevel
    have hp : 0 < A.freeLevel v.val := by rw [hf]; exact hRealPos
    exact (finiteNumericH_positive_freeLevel_ne_realPosition
      K k N v.val p k v.isLt hp) hf
  have hNotRight : LevelTree.meet ov ow ≠ ow := by
    intro heq
    have hf : A.freeLevel w.val = hPosition k p k := by
      calc
        A.freeLevel w.val = LevelTree.lev ow := rfl
        _ = LevelTree.lev (LevelTree.meet ov ow) := by rw [heq]
        _ = hPosition k p k := hMeetLevel
    have hp : 0 < A.freeLevel w.val := by rw [hf]; exact hRealPos
    exact (finiteNumericH_positive_freeLevel_ne_realPosition
      K k N w.val p k w.isLt hp) hf
  have hCharge : NumericHMeetCharge K.binary k v.val w.val p k :=
    finiteNumericH_prefix_meet_charge
      family K k N hk hAvoidA
      v.val w.val v.isLt w.isLt
      ov ow le_rfl le_rfl hCommon hNotLeft hNotRight
      p k hk le_rfl hMeetLevel
  rcases numericHMeetCharge_higher_original
      K.binary k v.val w.val p k hCharge with hv | hw
  · obtain ⟨_i,n,hn,_hRep,hHigher,_hFirst⟩ := hv
    omega
  · obtain ⟨_i,n,hn,_hRep,hHigher,_hFirst⟩ := hw
    omega

/-- If a real top-generation level has an actual I1 or I2
event, an INITIAL seed already occurs at that level.
A trivial I2 meet is treated as I1; a strict I2 meet cannot
be at generation k. -/
theorem numericHTopSeeds_real_top_I1I2_is_seed_level
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (I : Set Nat) (p : Nat)
    (hEvent :
      (∃ z : AdmissibleKptNode family,
        z ∈ SMTree.Envelope.closure (admissibleKptSTree family) I
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        LevelTree.lev z = hPosition k p k) ∨
      (∃ a : AdmissibleKptNode family,
        a ∈ SMTree.Envelope.closure (admissibleKptSTree family) I
          (numericHTopGenerationSeeds family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin) ∧
        ∃ b : AdmissibleKptNode family,
          b ∈ SMTree.Envelope.closure (admissibleKptSTree family) I
            (numericHTopGenerationSeeds family K k N
              (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
              c blocks hWithin) ∧
          SMTree.Envelope.SameComponent a b ∧
          LevelTree.lev (LevelTree.meet a b) = hPosition k p k)) :
    ∃ z : AdmissibleKptNode family,
      z ∈ numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin ∧
      LevelTree.lev z = hPosition k p k := by
  rcases hEvent with ⟨z,hz,hLev⟩ | ⟨a,ha,b,hb,hSame,hLev⟩
  · exact ⟨z,numericHTopSeeds_real_top_I1_is_seed
      family K hCarrier hAvoidK k N hk c blocks hWithin I
      z hz p hLev,hLev⟩
  · by_cases hLeft : LevelTree.meet a b = a
    · have hALev : LevelTree.lev a = hPosition k p k := by
        rw [←hLeft]
        exact hLev
      exact ⟨a,numericHTopSeeds_real_top_I1_is_seed
        family K hCarrier hAvoidK k N hk c blocks hWithin I
        a ha p hALev,hALev⟩
    · by_cases hRight : LevelTree.meet a b = b
      · have hBLev : LevelTree.lev b = hPosition k p k := by
          rw [←hRight]
          exact hLev
        exact ⟨b,numericHTopSeeds_real_top_I1_is_seed
          family K hCarrier hAvoidK k N hk c blocks hWithin I
          b hb p hBLev,hBLev⟩
      · have hSeedPool :=
          numericHTopGenerationSeeds_subset_rootPool
            family K k N
            (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
            c blocks hWithin
        exact False.elim
          (numericH_no_strict_closure_meet_at_top_generation
            family K hCarrier hAvoidK k N hk
            ({c} : Set (Fin N)) I
            (numericHTopGenerationSeeds family K k N
              (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
              c blocks hWithin)
            hSeedPool a b ha hb hSame hLeft hRight p hLev)

end SuccessorTree.V10
