import SuccessorTree.V10.I3SelectedStageSignature
import Mathlib.Tactic

/-!
# V10 I3: recover the selected original pool from the actual stage graph

The manuscript's genuine f_ell has a source consisting of selected
closure types, not all ambient original types crossing the cut.  A
source-to-original representation preserving BOTH the old type and
its complete next type is enough to reconstruct the correct selected
subset of one fixed finite original pool.  No independent hypothesis
about a chosen Selected predicate, source equality or target equality
is needed once this representation has been proved from the closure.

The predicate below selects exactly those ambient original names
whose old type belongs to the prescribed source, whose full next
type agrees with f_ell, and whose actual E-free level reaches the cut.
It is allowed to vary with ell; the finite universe Fin M stays fixed.

The remaining manuscript-specific lemma must establish the
source-to-original representation from Algorithm 5.4's closure,
prefix invariant and failure of (I2).  It is *not* asserted here.
-/

namespace SuccessorTree.V10

/-- An original name belongs to the selected graph iff it genuinely
represents a source/target pair of the given prescribed function.
This deliberately excludes ambient originals that merely have
a sufficiently long free cut but do not occur in the closure. -/
def selectedFromActualGraph
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (F : PrescribedBoringData ell db du dd)
    (v : Fin M) : Prop :=
  ell+1 ≤ A.freeLevel (original v).val ∧
  A.partialTypeAt ell (original v).val ∈ F.source ∧
  F.target (A.partialTypeAt ell (original v).val) =
    A.partialTypeAt (ell+1) (original v).val

/-- A single source-to-original representation hypothesis produces
both the exact selected source and the full next-type graph.
In particular, arbitrary duplicate old ambient types introduce
no ambiguity, because the actual prescribed F already determines
the next type. -/
theorem selectedFromActualGraph_source_iff
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (F : PrescribedBoringData ell db du dd)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        ell+1 ≤ A.freeLevel (original v).val ∧
        T = A.partialTypeAt ell (original v).val ∧
        F.target T = A.partialTypeAt (ell+1) (original v).val) :
    ∀ T, T ∈ F.source ↔
      T ∈ (selectedStagePoolPrescribedData
        A ell original (selectedFromActualGraph A ell original F)).source := by
  classical
  intro T
  constructor
  · intro hT
    obtain ⟨v,hCut,hOld,hNext⟩ := hRepresented T hT
    have hOldMem :
        A.partialTypeAt ell (original v).val ∈ F.source := by
      rw [←hOld]
      exact hT
    have hTarget :
        F.target (A.partialTypeAt ell (original v).val) =
          A.partialTypeAt (ell+1) (original v).val := by
      rw [←hOld]
      exact hNext
    change ∃ v : Fin M,
      (selectedFromActualGraph A ell original F v ∧
        ell+1 ≤ A.freeLevel (original v).val) ∧
      A.partialTypeAt ell (original v).val = T
    exact ⟨v,⟨⟨hCut,hOldMem,hTarget⟩,hCut⟩,hOld.symm⟩
  · intro hStage
    change ∃ v : Fin M,
      (selectedFromActualGraph A ell original F v ∧
        ell+1 ≤ A.freeLevel (original v).val) ∧
      A.partialTypeAt ell (original v).val = T at hStage
    obtain ⟨v,hv,hOld⟩ := hStage
    have hMem := hv.1.2.1
    simpa only [hOld] using hMem

/-- The selected predicate already encodes the full target graph.
No additional next-type equation is postulated. -/
theorem selectedFromActualGraph_target
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (F : PrescribedBoringData ell db du dd)
    (v : Fin M)
    (hv : selectedFromActualGraph A ell original F v) :
    F.target (A.partialTypeAt ell (original v).val) =
      A.partialTypeAt (ell+1) (original v).val := hv.2.2

/-- Exactly the manuscript's corrected finite L-age test transfers
to the reconstructed selected original pool.  There is no claim that
an all-eligible pool has the same B3 test. -/
theorem correctedB3_iff_selectedFromActualGraph
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (F : PrescribedBoringData ell db du dd)
    (hRepresented : ∀ T, T ∈ F.source →
      ∃ v : Fin M,
        ell+1 ≤ A.freeLevel (original v).val ∧
        T = A.partialTypeAt ell (original v).val ∧
        F.target T = A.partialTypeAt (ell+1) (original v).val) :
    F.CorrectedB3 family ↔
      (selectedStagePoolPrescribedData
        A ell original (selectedFromActualGraph A ell original F)).CorrectedB3 family := by
  apply selectedStagePool_B3_iff_of_source_and_graph
    family A ell original (selectedFromActualGraph A ell original F)
    F
  · exact selectedFromActualGraph_source_iff
      A ell original F hRepresented
  · intro v hv _hCut
    exact selectedFromActualGraph_target A ell original F v hv

/-- Observation 6.52 directly from the manuscript's original-valued
SOURCE REPRESENTATION, with NO explicit selected-predicate,
source-equality, graph-equality or signature-injectivity hypotheses.

The further concrete obligation is to obtain hRepresented for
Algorithm 5.4's actual f_ell by tracing its source closure. -/
theorem actualRepresentedI3_failure_levels_card_le_signature_capacity
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (original : Fin M → Fin A.size)
    (F : (ell : Nat) → PrescribedBoringData ell db du dd)
    (levels : Finset Nat)
    (hFailed : ∀ ell, ell ∈ levels →
      ell < A.size ∧ ¬ (F ell).CorrectedB3 family)
    (hRepresented : ∀ ell, ell ∈ levels →
      ∀ T, T ∈ (F ell).source →
        ∃ v : Fin M,
          ell+1 ≤ A.freeLevel (original v).val ∧
          T = A.partialTypeAt ell (original v).val ∧
          (F ell).target T =
            A.partialTypeAt (ell+1) (original v).val) :
    levels.card ≤
      ageSignatureCapacity
        (fun i : Fin family.length => (family.get i).patternCard) M := by
  let Selected : Nat → Fin M → Prop :=
    fun ell v => selectedFromActualGraph A ell original (F ell) v
  apply actualSelectedStage_B3_failure_levels_card_le_signature_capacity
    family A original Selected F levels hFailed
  · intro ell hEll T
    exact selectedFromActualGraph_source_iff
      A ell original (F ell) (hRepresented ell hEll) T
  · intro ell _hEll v hv _hCut
    exact selectedFromActualGraph_target A ell original (F ell) v hv

end SuccessorTree.V10
