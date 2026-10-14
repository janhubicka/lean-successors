import SuccessorTree.V10.HActualGenerationEventBound
import Mathlib.Tactic

/-!
# V10 Proposition 6.44: higher original names are counted by higher levels

The geometric induction step gives |S_r| <= H_r + R(H_r),
where H_r is the finite set of higher-generation original
ADDRESSES in one final AlgorithmRun stage pool V.

To apply the manuscript's downward induction, H_r must be
bounded by the one root c plus already selected real levels
of generations m>r. This is not a new Ramsey statement.

Every member of V is either c, or has address i in the final
selected set I with positive E-free cut. Thus every member
of H_r apart from c has both a selected actual address and
a unique real H-generation m>r. Its address belongs to the
finite selected generation-m level set S_m. The count uses
the disjoint address representation, never quotients equal
partial types. Consequently

    |H_r| <= 1 + sum_{m=r+1}^k |S_m|.

This supplies the missing numerical comparison used by the
manuscript recurrence. No extra higher-generation naming
hypothesis is assumed.
-/

namespace SuccessorTree.V10

/-- The subset of actual selected original addresses at real
generations strictly greater than r, excluding any exceptional
root address c which need not itself be selected. -/
noncomputable def numericHSelectedHigherAddresses
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (r : Nat) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun v : Fin N =>
    v.val ∈ R.I 0 ∧
      ∃ p m : Nat, r < m ∧ m ≤ k ∧
        v.val = hPosition k p m)

/-- Every higher-generation original in the final retained pool
is either the distinguished root c or an actual SELECTED higher
real address. -/
theorem numericHHighOriginals_subset_root_or_selected
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (r : Nat) :
    hGenerationHighOriginals k r
        (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))
      ⊆
    ({c} : Finset (Fin N)) ∪
      numericHSelectedHigherAddresses family K k N c X R r := by
  classical
  intro v hv
  have hData :
      v ∈ hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0) ∧
      (∃ p m : Nat, r < m ∧ m ≤ k ∧
        v.val = hPosition k p m) := by
    simpa only [hGenerationHighOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and] using hv
  obtain ⟨hV,hReal⟩ := hData
  have hStage :
      v = c ∨ (v.val ∈ R.I 0 ∧
        0 < (finiteNumericH K k N).freeLevel v.val) := by
    simpa only [hStageOriginals, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton,
      Set.mem_ofPred_eq] using hV
  rcases hStage with hRoot | ⟨hSelected,_hFree⟩
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr hRoot))
  · refine Finset.mem_union.mpr (Or.inr ?_)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hSelected,hReal⟩

/-- The selected higher addresses lie in the union of the
generation-m selected address sets, for r<m<=k. This relies on
their LITERAL positions, not on equivalence of partial types. -/
theorem numericHSelectedHigherAddresses_subset_generationUnion
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (r : Nat) :
    numericHSelectedHigherAddresses family K k N c X R r ⊆
      (Finset.Icc (r+1) k).biUnion
        (fun m => (Finset.univ : Finset (Fin N)).filter
          (fun v => v.val ∈ R.I 0 ∧
            ∃ p : Nat, v.val = hPosition k p m)) := by
  classical
  intro v hv
  have hData := (Finset.mem_filter.mp hv).2
  obtain ⟨hSelected,p,m,hrm,hmk,hReal⟩ := hData
  apply Finset.mem_biUnion.mpr
  refine ⟨m, Finset.mem_Icc.mpr ⟨by omega,hmk⟩,?_⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hSelected,p,hReal⟩

/-- At a fixed generation m, taking literal addresses
Fin N -> Nat injects the selected original-address set into
the actual AlgorithmRun selected real-level set S_m. -/
theorem numericHSelectedGenerationAddresses_card_le_levels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (m : Nat) :
    ((Finset.univ : Finset (Fin N)).filter
      (fun v => v.val ∈ R.I 0 ∧
        ∃ p : Nat, v.val = hPosition k p m)).card ≤
      (numericHSelectedRealGenerationLevels
        family K k N c X R m).card := by
  classical
  let T : Finset (Fin N) := Finset.univ.filter
    (fun v => v.val ∈ R.I 0 ∧
      ∃ p : Nat, v.val = hPosition k p m)
  have hInjective : Set.InjOn Fin.val (T : Set (Fin N)) := by
    intro a _ b _ h
    exact Fin.ext h
  have hCard : T.card = (T.image Fin.val).card :=
    (Finset.card_image_iff.mpr hInjective).symm
  have hSub : T.image Fin.val ⊆
      numericHSelectedRealGenerationLevels family K k N c X R m := by
    intro ell hEll
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hEll
    obtain ⟨hSel,p,hReal⟩ := (Finset.mem_filter.mp hv).2
    have hTop :
        v.val ≤ (finiteNumericH K k N).freeLevel c.val :=
      (R.I_mem_bounds 0 (Nat.zero_le _) v.val hSel).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (by omega)
    · exact ⟨hSel,p,hReal⟩
  exact hCard.trans (Finset.card_le_card hSub)

/-- The induction's critical higher-pool estimate: one root plus
actual selected real levels in strictly higher generations bound
all higher original ADDRESSES in the fixed final stage pool. -/
theorem numericHHighOriginals_card_le_higherSelectedLevels
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat) (c : Fin N)
    (X : Set (AdmissibleKptNode family))
    (R : SMTree.Envelope.AlgorithmRun
      (normalizedKptSMTree family) X
      ((finiteNumericH K k N).freeLevel c.val))
    (r : Nat) :
    (hGenerationHighOriginals k r
      (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))).card
      ≤ 1 +
      ∑ m ∈ Finset.Icc (r+1) k,
        (numericHSelectedRealGenerationLevels
          family K k N c X R m).card := by
  classical
  let B : Finset (Fin N) :=
    numericHSelectedHigherAddresses family K k N c X R r
  let Gen : Nat → Finset (Fin N) := fun m =>
    (Finset.univ : Finset (Fin N)).filter
      (fun v => v.val ∈ R.I 0 ∧
        ∃ p : Nat, v.val = hPosition k p m)
  have hGenSub : B ⊆ (Finset.Icc (r+1) k).biUnion Gen :=
    numericHSelectedHigherAddresses_subset_generationUnion
      family K k N c X R r
  have hGenCard :
      B.card ≤ ∑ m ∈ Finset.Icc (r+1) k,
        (numericHSelectedRealGenerationLevels
          family K k N c X R m).card := by
    calc
      B.card ≤ ((Finset.Icc (r+1) k).biUnion Gen).card :=
        Finset.card_le_card hGenSub
      _ ≤ ∑ m ∈ Finset.Icc (r+1) k, (Gen m).card :=
        Finset.card_biUnion_le _ _
      _ ≤ ∑ m ∈ Finset.Icc (r+1) k,
          (numericHSelectedRealGenerationLevels
            family K k N c X R m).card := by
        apply Finset.sum_le_sum
        intro m hm
        exact numericHSelectedGenerationAddresses_card_le_levels
          family K k N c X R m
  have hHighSub :
      hGenerationHighOriginals k r
          (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))
        ⊆ ({c} : Finset (Fin N)) ∪ B :=
    numericHHighOriginals_subset_root_or_selected
      family K k N c X R r
  calc
    (hGenerationHighOriginals k r
        (hStageOriginals K k N ({c} : Finset (Fin N)) (R.I 0))).card
      ≤ (({c} : Finset (Fin N)) ∪ B).card :=
        Finset.card_le_card hHighSub
    _ ≤ 1 + B.card := by
      simpa using Finset.card_union_le ({c} : Finset (Fin N)) B
    _ ≤ 1 + ∑ m ∈ Finset.Icc (r+1) k,
        (numericHSelectedRealGenerationLevels
          family K k N c X R m).card :=
      Nat.add_le_add_left hGenCard 1

end SuccessorTree.V10