import SuccessorTree.V10.ConcreteOriginalPool
import SuccessorTree.V10.OriginalPoolEnvelope
import Mathlib.Tactic

/-!
# Section 6: exact normal form of the finite original-pool closure

The closure in Algorithm 5.4 is the LEAST set containing the
initial seeds and closed under componentwise meets and parameters
at selected levels.  Prefix representation alone does not say
whether a positive-generation node selected by (I1) is a genuine
meet.  The missing step is to show that EVERY closure node is one
of only three kinds:

1. an initial seed node;
2. the unique complete parameter type at a selected level with
   positive E-free cut;
3. a meet of two complete ambient ORIGINAL types from the
   maintained finite pool.

The third category includes arbitrary iterations of meet
closure. The proof uses closure minimality: this three-way
normal-form set is closed under further meets because a new
nontrivial meet of represented prefixes is already a meet of
originals; it is closed under parameters because an actual
Kpt successor along a represented prefix has exactly the
empty-or-singleton ambient parameter record.

For the eventual Proposition 6.44 induction it remains to show
that the first two categories cannot have a REAL H level of
intermediate positive generation r. This uses the chosen seed
levels and the verified odd free-cut geometry of numerical H.
The resulting positive (I1) levels will then be genuine meets
charged by Corollary 6.50.
-/

namespace SuccessorTree.V10

/-- A one-stage closure node is a seed, an actually selected
ambient parameter node, or a meet of two ambient originals.
No extra downward-prefix operation is silently included. -/
def kptStageClosureNormalForm
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (V : Set (Fin A.size)) : Set (AdmissibleKptNode family) :=
  {z | z ∈ X ∨
    (∃ i : Fin A.size,
      i.val ∈ I ∧ 0 < A.freeLevel i.val ∧
      z = A.kptOriginal family hAvoid i) ∨
    (∃ v : Fin A.size, v ∈ V ∧
      ∃ w : Fin A.size, w ∈ V ∧
        SMTree.Envelope.SameComponent
          (A.kptOriginal family hAvoid v)
          (A.kptOriginal family hAvoid w) ∧
        z = LevelTree.meet
          (A.kptOriginal family hAvoid v)
          (A.kptOriginal family hAvoid w))}

/-- The three-way normal form itself uses no new original outside
the maintained pool. -/
theorem kptStageClosureNormalForm_subset_pool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hSelected : ∀ i : Fin A.size, i.val ∈ I →
      0 < A.freeLevel i.val → i ∈ V) :
    kptStageClosureNormalForm family A hAvoid I X V ⊆
      ambientPrefixPool family A hAvoid V := by
  intro z hz
  rcases hz with hzSeed | hzParam | hzMeet
  · exact (ambientPrefixPool_mono family A hAvoid hUV) (hX hzSeed)
  · obtain ⟨i,hi,hFree,rfl⟩ := hzParam
    exact ⟨A.kptOriginal family hAvoid i,
      ⟨i,hSelected i hi hFree,rfl⟩,le_rfl⟩
  · obtain ⟨v,hv,w,hw,hCommon,rfl⟩ := hzMeet
    exact ⟨A.kptOriginal family hAvoid v,
      ⟨v,hv,rfl⟩,LevelTree.meet_le_left hCommon⟩

/-- Further meets add no fourth kind of node: each nontrivial
meet of prefixes of originals is precisely the meet of two
originals in the same fixed stage pool. -/
theorem kptStageClosureNormalForm_meetClosed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hSelected : ∀ i : Fin A.size, i.val ∈ I →
      0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.MeetClosed
      (kptStageClosureNormalForm family A hAvoid I X V) := by
  intro s t hs ht hCommon
  by_cases hLeft : LevelTree.meet s t = s
  · rw [hLeft]
    exact hs
  by_cases hRight : LevelTree.meet s t = t
  · rw [hRight]
    exact ht
  have hRep := kptStageClosureNormalForm_subset_pool
    family A hAvoid I X U V hX hUV hSelected
  obtain ⟨p,⟨v,hv,rfl⟩,hsp⟩ := hRep hs
  obtain ⟨q,⟨w,hw,rfl⟩,htq⟩ := hRep ht
  obtain ⟨op,hop,oq,hoq,hOriginalCommon,hMeetEq⟩ :=
    nontrivial_meet_has_originals
      (V := (A.kptOriginal family hAvoid) '' V)
      ⟨p,⟨v,hv,rfl⟩,hsp⟩
      ⟨q,⟨w,hw,rfl⟩,htq⟩
      hCommon hLeft hRight
  obtain ⟨v',hv',hOp⟩ := hop
  obtain ⟨w',hw',hOq⟩ := hoq
  subst op
  subst oq
  exact Or.inr (Or.inr
    ⟨v',hv',w',hw',hOriginalCommon,hMeetEq⟩)

/-- All selected successor parameters of a represented prefix
are exactly complete ambient original types of vertices with
positive E-free cut. Hence the normal form is closed under
the ACTUAL Kpt successor parameters, not an abstract assumed
parameter map. -/
theorem kptStageClosureNormalForm_parameterClosed
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hSelected : ∀ i : Fin A.size, i.val ∈ I →
      0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.ParameterClosedOver (admissibleKptSTree family)
      (kptStageClosureNormalForm family A hAvoid I X V) I := by
  intro a ha i hi hia p c hStep x hx
  have hRep := kptStageClosureNormalForm_subset_pool
    family A hAvoid I X U V hX hUV hSelected
  obtain ⟨o,⟨v,hv,rfl⟩,hAo⟩ := hRep ha
  obtain ⟨hiSize,hParam⟩ :=
    admissibleKpt_crossing_parameter
      family A hAvoid v a hAo i hia p c hStep
  have hMem : x.val ∈ p.map Subtype.val :=
    List.mem_map.mpr ⟨x,hx,rfl⟩
  rw [hParam] at hMem
  by_cases hZero : A.freeLevel i = 0
  · simp [hZero] at hMem
  · have hPos : 0 < A.freeLevel i := by omega
    have hRaw : x.val = A.rawTypeAtFree i := by
      simpa [hZero] using hMem
    let vi : Fin A.size := ⟨i,hiSize⟩
    have hOrig : x = A.kptOriginal family hAvoid vi :=
      Subtype.ext hRaw
    exact Or.inr (Or.inl ⟨vi,hi,hPos,hOrig⟩)

/-- Minimality of the actual Section 5 closure gives a
three-way normal form for EVERY one of its nodes, regardless
of how many meet/parameter operations were needed. -/
theorem admissibleKpt_stage_closure_normalForm
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U V : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (hUV : U ⊆ V)
    (hSelected : ∀ i : Fin A.size, i.val ∈ I →
      0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      kptStageClosureNormalForm family A hAvoid I X V := by
  apply SMTree.Envelope.closure_minimal
    (admissibleKptSTree family) I X
    (kptStageClosureNormalForm family A hAvoid I X V)
  · intro x hx
    exact Or.inl hx
  · exact kptStageClosureNormalForm_meetClosed
      family A hAvoid I X U V hX hUV hSelected
  · exact kptStageClosureNormalForm_parameterClosed
      family A hAvoid I X U V hX hUV hSelected

/-- Apply the normal form with the concrete maintained stage
pool: all seed originals together with the selected vertices
whose Kpt successor parameter is nonempty. -/
theorem admissibleKpt_actual_stage_closure_normalForm
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      kptStageClosureNormalForm family A hAvoid I X
        (ambientStagePool A U I) := by
  apply admissibleKpt_stage_closure_normalForm
    family A hAvoid I X U (ambientStagePool A U I) hX
  · intro v hv
    exact Or.inl hv
  · intro i hi hPos
    exact Or.inr ⟨hi,hPos⟩

/-- Every actual closure node which is neither an initial seed nor
a selected parameter is ALREADY a meet of two original types from
the maintained pool. This is the outstanding (I1) classification
step before excluding the seed/parameter cases by numerical
H-generation parity. -/
theorem admissibleKpt_actual_closure_node_original_meet
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat)
    (X : Set (AdmissibleKptNode family))
    (U : Set (Fin A.size))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U)
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I X)
    (hNotSeed : z ∉ X)
    (hNotParam : ¬ ∃ i : Fin A.size,
      i.val ∈ I ∧ 0 < A.freeLevel i.val ∧
      z = A.kptOriginal family hAvoid i) :
    ∃ v : Fin A.size, v ∈ ambientStagePool A U I ∧
      ∃ w : Fin A.size, w ∈ ambientStagePool A U I ∧
        SMTree.Envelope.SameComponent
          (A.kptOriginal family hAvoid v)
          (A.kptOriginal family hAvoid w) ∧
        z = LevelTree.meet
          (A.kptOriginal family hAvoid v)
          (A.kptOriginal family hAvoid w) := by
  have hNF :=
    admissibleKpt_actual_stage_closure_normalForm
      family A hAvoid I X U hX hz
  rcases hNF with hSeed | hParam | hMeet
  · exact False.elim (hNotSeed hSeed)
  · exact False.elim (hNotParam hParam)
  · exact hMeet

end SuccessorTree.V10
