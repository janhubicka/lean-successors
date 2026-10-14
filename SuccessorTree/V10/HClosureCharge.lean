import SuccessorTree.V10.ConcreteOriginalPool
import SuccessorTree.V10.HFiniteAge

/-!
# Positive-generation charges throughout the actual envelope closure

The concrete original-pool invariant and the actual H meet theorem now
apply together, with both represented originals chosen inside the maintained
stage pool. Iterated parameter and meet closure introduce no new origins.
For a fixed positive generation r, one higher-generation original determines
at most one charged level. A finite image therefore supplies a linear
per-generation bound, rather than a quadratic pair budget.

This is not yet the complete I1/I2/I3 envelope recurrence: signature/age
obstructions and the global M2/M3 constructions remain separate.
-/

namespace SuccessorTree.V10

/-- Every positive-generation nontrivial meet in the ACTUAL closure is
charged to originals in the maintained seed-plus-selected stage pool. -/
theorem forbiddenFreeH_closure_meet_charge
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hk : 0 < k)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K)
    (U : Set (Fin N)) (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoid) U)
    (s t : AdmissibleKptNode family)
    (hs : s ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X)
    (ht : t ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X)
    (hCommon : ∃ c : AdmissibleKptNode family, c ≤ s ∧ c ≤ t)
    (hStrictS : LevelTree.meet s t ≠ s) (hStrictT : LevelTree.meet s t ≠ t)
    (p r : Nat) (hr : 0 < r) (hrk : r ≤ k)
    (hMeet : LevelTree.lev (LevelTree.meet s t) = hPosition k p r) :
    ∃ v w : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      w ∈ ambientStagePool (finiteNumericH K k N) U I ∧
      NumericHMeetCharge K.binary k v.val w.val p r := by
  have hPool := admissibleKpt_stage_closure_subset_pool family
    (finiteNumericH K k N)
    (finiteNumericH_avoids_family family K hCarrier k N hAvoid) U I X hX
  obtain ⟨ov, ⟨v, hv, rfl⟩, hsv⟩ := hPool hs
  obtain ⟨ow, ⟨w, hw, rfl⟩, htw⟩ := hPool ht
  exact ⟨v, w, hv, hw,
    forbiddenFreeH_prefix_meet_charge family K hCarrier k N hk hAvoid
      v.val w.val v.isLt w.isLt s t hsv htw hCommon hStrictS hStrictT p r hr hrk hMeet⟩

/-- A higher-generation original determines its charged block by its
least incident base neighbour, including both directed orientations. -/
def HOriginalCharge {db : Nat} (B : Nat → Nat → Fin db → Bool)
    (k r v p : Nat) : Prop :=
  ∃ i n : Nat, n ≤ k ∧ v = hPosition k i n ∧ r < n ∧
    FirstBinaryNeighbour (bidirectionalBits B) i p

theorem firstBinaryNeighbour_unique
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (i p q : Nat)
    (hp : FirstBinaryNeighbour B i p) (hq : FirstBinaryNeighbour B i q) : p = q := by
  by_contra hne
  have hcases : p < q ∨ q < p := by omega
  rcases hcases with hpq | hqp
  · obtain ⟨a, ha⟩ := hp.2.1
    have hf := hq.2.2 p hpq a
    rw [ha] at hf
    contradiction
  · obtain ⟨a, ha⟩ := hq.2.1
    have hf := hp.2.2 q hqp a
    rw [ha] at hf
    contradiction

/-- Retaining addresses rather than deduplicating types makes the
uniqueness of an original's charge immediate from bounded iota injectivity. -/
theorem hOriginalCharge_unique
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k r v p q : Nat)
    (hp : HOriginalCharge B k r v p) (hq : HOriginalCharge B k r v q) : p = q := by
  obtain ⟨i, n, hn, hv, _, hp⟩ := hp
  obtain ⟨j, m, hm, hw, _, hq⟩ := hq
  obtain ⟨hij, _⟩ := hPosition_injective_bounded k i n j m hn hm (hv.symm.trans hw)
  subst j
  exact firstBinaryNeighbour_unique (bidirectionalBits B) i p q hp hq

theorem numericHMeetCharge_higher_original
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k v w p r : Nat)
    (h : NumericHMeetCharge B k v w p r) :
    HOriginalCharge B k r v p ∨ HOriginalCharge B k r w p := by
  obtain ⟨i, j, n, m, hv, hw, _hn, _hm, hnk, hmk, _hpi, _hpj, hcases⟩ := h
  rcases hcases with ⟨hr, hmn, _hguard, hfirst⟩ | ⟨hr, hnm, _hguard, hfirst⟩
  · exact Or.inl ⟨i, n, hnk, hv, by omega, hfirst⟩
  · exact Or.inr ⟨j, m, hmk, hw, by omega, hfirst⟩

/-- A total index is used only to write the finite image budget. Its
default value is never used for an original actually carrying a charge. -/
noncomputable def hOriginalChargeIndex
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k r v : Nat) : Nat := by
  classical
  exact if h : ∃ p, HOriginalCharge B k r v p then Classical.choose h else 0

theorem hOriginalChargeIndex_eq
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k r v p : Nat)
    (hp : HOriginalCharge B k r v p) : hOriginalChargeIndex B k r v = p := by
  classical
  have h : ∃ q, HOriginalCharge B k r v q := ⟨p, hp⟩
  simp only [hOriginalChargeIndex, dite_eq_left h]
  exact hOriginalCharge_unique B k r v _ p (Classical.choose_spec h) hp

/-- Only higher-generation originals with an incident base neighbour
can pay for a meet at generation r. -/
noncomputable def hHigherOriginals
    {db N : Nat} (B : Nat → Nat → Fin db → Bool) (k r : Nat)
    (V : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact V.filter (fun v => ∃ p, HOriginalCharge B k r v.val p)

noncomputable def hPoolChargeLevels
    {db N : Nat} (B : Nat → Nat → Fin db → Bool) (k r : Nat)
    (V : Finset (Fin N)) : Finset Nat := by
  classical
  exact (hHigherOriginals B k r V).image
    (fun v => hPosition k (hOriginalChargeIndex B k r v.val) r)

theorem hPoolChargeLevels_card_le
    {db N : Nat} (B : Nat → Nat → Fin db → Bool) (k r : Nat)
    (V : Finset (Fin N)) :
    (hPoolChargeLevels B k r V).card ≤ (hHigherOriginals B k r V).card := by
  classical
  exact Finset.card_image_le

theorem hOriginalCharge_level_mem_budget
    {db N : Nat} (B : Nat → Nat → Fin db → Bool) (k r : Nat)
    (V : Finset (Fin N)) (v : Fin N) (hv : v ∈ V) (p : Nat)
    (hp : HOriginalCharge B k r v.val p) : hPosition k p r ∈ hPoolChargeLevels B k r V := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨v, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hv, ⟨p, hp⟩⟩
  · rw [hOriginalChargeIndex_eq B k r v.val p hp]

/-- A finite stage pool, with original addresses and the exact free-cut
condition. It is definitionally the finite counterpart of ambientStagePool. -/
noncomputable def hStageOriginals
    {db du dd : Nat} (K : AgeTestModel db du dd) (k N : Nat)
    (U : Finset (Fin N)) (I : Set Nat) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v => v ∈ U ∨
    (v.val ∈ I ∧ 0 < (finiteNumericH K k N).freeLevel v.val))

/-- Corollary 6.50 in the exact normalized model: all generation-r
nontrivial meet levels from the ACTUAL closure fit in a finite budget of
size at most the number of eligible higher originals in the stage pool.
No parameter-closure or meet-charging assumption remains. -/
theorem forbiddenFreeH_closure_meet_budget
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k N : Nat) (hk : 0 < k)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids K)
    (U : Finset (Fin N)) (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family (finiteNumericH K k N)
      (finiteNumericH_avoids_family family K hCarrier k N hAvoid) (U : Set (Fin N)))
    (r : Nat) (hr : 0 < r) (hrk : r ≤ k) :
    ∃ D : Finset Nat,
      D.card ≤ (hHigherOriginals K.binary k r (hStageOriginals K k N U I)).card ∧
      ∀ s t : AdmissibleKptNode family,
        s ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X →
        t ∈ SMTree.Envelope.closure (admissibleKptSTree family) I X →
        (∃ c : AdmissibleKptNode family, c ≤ s ∧ c ≤ t) →
        LevelTree.meet s t ≠ s → LevelTree.meet s t ≠ t →
        ∀ p : Nat, LevelTree.lev (LevelTree.meet s t) = hPosition k p r →
          LevelTree.lev (LevelTree.meet s t) ∈ D := by
  classical
  let V := hStageOriginals K k N U I
  refine ⟨hPoolChargeLevels K.binary k r V, hPoolChargeLevels_card_le K.binary k r V, ?_⟩
  intro s t hs ht hc hss hst p hMeet
  obtain ⟨v, w, hv, hw, hCharge⟩ := forbiddenFreeH_closure_meet_charge
    family K hCarrier k N hk hAvoid (U : Set (Fin N)) I X hX
    s t hs ht hc hss hst p r hr hrk hMeet
  have hvV : v ∈ V := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  have hwV : w ∈ V := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
  rw [hMeet]
  rcases numericHMeetCharge_higher_original K.binary k v.val w.val p r hCharge with h | h
  · exact hOriginalCharge_level_mem_budget K.binary k r V v hvV p h
  · exact hOriginalCharge_level_mem_budget K.binary k r V w hwV p h

end SuccessorTree.V10
