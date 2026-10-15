import SuccessorTree.V10.ForestMeetLinear
import SuccessorTree.V10.KptStageClosureNormalForm
import Mathlib.Tactic

/-!
# V10: actual Kpt stage closure uses at most 2(|seeds|+|originals|) levels

The generic sharp forest meet count is useful only after proving
that the ACTUAL Section 5 closure belongs to that generated
finite set. This module makes the transfer with no extra
closure-finiteness or graph assumption.

For a finite seed set X represented by original seed addresses U,
and a finite larger pool V containing U and all selected positive
E-free-cut parameter originals, the existing exact Kpt closure
normal form proves that every closure node is:
- one of the seed nodes X;
- the complete type of a parameter original from V; or
- the componentwise meet of two such original types from V.

Thus every closure node belongs to the componentwise pair-meet
set of the finite generator P = X union {fullType(v):v in V}.
The sharp generic forest estimate then gives at most 2|P|,
hence 2(|X|+|V|) nodes, and no more distinct levels.

This is exactly the sharp meet part of the final bound of
Proposition 6.44. I3 age-change levels are counted separately.
-/

namespace SuccessorTree.V10

/-- Actual finite generating nodes at one Kpt closure stage:
the literal seeds together with each retained full original. -/
noncomputable def finiteKptClosureGeneratorPool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (X : Finset (AdmissibleKptNode family))
    (V : Finset (Fin A.size)) :
    Finset (AdmissibleKptNode family) := by
  classical
  exact X ∪ V.image (A.kptOriginal family hAvoid)

/-- Concrete closure, not an abstract assumed meet closure:
every actual Kpt closure node is an original seed or a
componentwise meet of two nodes of the finite generator pool. -/
theorem actualKptStageClosure_subset_forestMeetNodes
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Finset (AdmissibleKptNode family))
    (U V : Finset (Fin A.size))
    (hSeeds : (X : Set (AdmissibleKptNode family)) ⊆
      ambientPrefixPool family A hAvoid (U : Set (Fin A.size)))
    (hUV : U ⊆ V)
    (hParams : ∀ i : Fin A.size, i.val ∈ I →
      0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.closure
        (admissibleKptSTree family) I
        (X : Set (AdmissibleKptNode family)) ⊆
      (forestFiniteMeetNodes
        (finiteKptClosureGeneratorPool family A hAvoid X V) :
          Set (AdmissibleKptNode family)) := by
  classical
  let P := finiteKptClosureGeneratorPool family A hAvoid X V
  have hStageToV :
      ∀ i : Fin A.size, i ∈ ambientStagePool A
        (U : Set (Fin A.size)) I → i ∈ V := by
    intro i hi
    rcases hi with hu | ⟨hSelected,hFree⟩
    · exact hUV (Finset.mem_coe.mp hu)
    · exact hParams i hSelected hFree
  intro z hz
  have hNF :=
    admissibleKpt_actual_stage_closure_normalForm
      family A hAvoid I (X : Set (AdmissibleKptNode family))
      (U : Set (Fin A.size)) hSeeds hz
  rcases hNF with hSeed | hParam | hMeet
  · have hSeedP : z ∈ P :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_coe.mp hSeed))
    exact (forestFiniteMeetNodes_mem_iff P z).2 (Or.inl hSeedP)
  · obtain ⟨i,hi,hPos,rfl⟩ := hParam
    have hiV : i ∈ V :=
      hStageToV i (Or.inr ⟨hi,hPos⟩)
    have hiP : A.kptOriginal family hAvoid i ∈ P :=
      Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨i,hiV,rfl⟩))
    exact (forestFiniteMeetNodes_mem_iff P _).2 (Or.inl hiP)
  · obtain ⟨v,hv,w,hw,hSame,rfl⟩ := hMeet
    have hvV : v ∈ V := hStageToV v hv
    have hwV : w ∈ V := hStageToV w hw
    have hvP : A.kptOriginal family hAvoid v ∈ P :=
      Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨v,hvV,rfl⟩))
    have hwP : A.kptOriginal family hAvoid w ∈ P :=
      Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨w,hwV,rfl⟩))
    exact (forestFiniteMeetNodes_mem_iff P _).2
      (Or.inr ⟨A.kptOriginal family hAvoid v,hvP,
        A.kptOriginal family hAvoid w,hwP,hSame,rfl⟩)

/-- The sharp forest bound applies to this exact finite Kpt
generator pool, with no need for a quadratic pair estimate. -/
theorem finiteKptClosureGeneratorPool_forest_card_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (X : Finset (AdmissibleKptNode family))
    (V : Finset (Fin A.size)) :
    (forestFiniteMeetNodes
      (finiteKptClosureGeneratorPool family A hAvoid X V)).card
        ≤ 2 * (X.card + V.card) := by
  classical
  let P := finiteKptClosureGeneratorPool family A hAvoid X V
  have hPBound : P.card ≤ X.card + V.card := by
    calc
      P.card ≤ X.card + (V.image (A.kptOriginal family hAvoid)).card := by
        exact Finset.card_union_le _ _
      _ ≤ X.card + V.card :=
        Nat.add_le_add_left Finset.card_image_le _
  exact (forestFiniteMeetNodes_card_le_twice P).trans
    (Nat.mul_le_mul_left 2 hPBound)

/-- Even after forgetting the nodes and counting only their
real levels, the sharp bound remains 2(|seeds|+|originals|). -/
theorem finiteKptClosureGeneratorPool_levels_card_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (X : Finset (AdmissibleKptNode family))
    (V : Finset (Fin A.size)) :
    ((forestFiniteMeetNodes
      (finiteKptClosureGeneratorPool family A hAvoid X V)).image
        LevelTree.lev).card ≤ 2 * (X.card + V.card) :=
  Finset.card_image_le.trans
    (finiteKptClosureGeneratorPool_forest_card_le family A hAvoid X V)

end SuccessorTree.V10