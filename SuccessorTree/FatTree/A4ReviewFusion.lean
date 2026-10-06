import SuccessorTree.FatTree.A4PairPersistence

/-!
# Fixed-source fusion in the review proof of A4

This file isolates the persistence and fixed-source fusion machinery from
the local two-block combinatorics.  The generic core accepts a dense supply
of good pairs; a compatibility wrapper states the older
`ReviewGoodPairPrinciple` interface.  The completed source-letter proof in
`A4ReviewGoodPair` and `A4ReviewSourceFusion` reuses the same core.

Pair persistence is derived by finite-depth avoidance and metric fusion.
Last-block factorisation, rather than first-head factorisation, is used by the
final geometric coverage theorem.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- The local finite-prefix statement in `lem:trace-good-pair`.
Unlike A4, it asks only for two compatible blocks. -/
def ReviewGoodPairPrinciple : Prop :=
  ∀ (c n : Nat) (y : FiniteFatTree H) (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c)
    (O : Set (AM H c 1)) (U : FatTree H),
    ExtendsStem H y U →
    OneBlockLarge H y U (FixedTraceGoodRows H c n y hn hsrc O) →
    ∃ h k, FixedTraceGoodPair H c n y hn hsrc O h k ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y h) U k

/-- Package the fixed-source large-set invariant without exposing its proof
fields to rewrites of a finite prefix. -/
def ReviewTraceLarge (c n : Nat) (O : Set (AM H c 1))
    (y : FiniteFatTree H) (U : FatTree H) : Prop :=
  ∃ (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c),
      OneBlockLarge H y U (FixedTraceGoodRows H c n y hn hsrc O)

/-- The selected row is good after every exact trace of the current prefix. -/
def ReviewTraceGood (c n : Nat) (O : Set (AM H c 1))
    (y : FiniteFatTree H) (h : AM H y.terminalCut 1) : Prop :=
  ∃ (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c),
      h ∈ FixedTraceGoodRows H c n y hn hsrc O

/-- A finite prefix ends with a selected good row. This is a predicate on
the finite prefix alone, so exact fusion preserves it. -/
def ReviewStepGood (c n : Nat) (O : Set (AM H c 1))
    (z : FiniteFatTree H) : Prop :=
  ∃ (y : FiniteFatTree H) (h : AM H y.terminalCut 1),
    z = FiniteFatTree.appendRow H y h ∧ ReviewTraceGood H c n O y h

/-- Core persistence step.  The only local input is a supply of good
two-block pairs in every stem-preserving reduction.  The finite-depth
Baumgartner argument below turns that dense pair supply into a large
continuation.  Separating this core avoids duplicating the persistence proof
for the abstract and source-letter versions of the good-pair lemma. -/
theorem review_trace_persistence_core
    (c n : Nat) (O : Set (AM H c 1))
    (y : FiniteFatTree H) (U : FatTree H)
    (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c)
    (hyU : ExtendsStem H y U)
    (hlarge :
      OneBlockLarge H y U (FixedTraceGoodRows H c n y hn hsrc O))
    (hpairs : ∀ A : FatTree H, Reduces H A U → ExtendsStem H y A →
      ∃ h k, FixedTraceGoodPair H c n y hn hsrc O h k ∧
        OneBlockOccurs H (FiniteFatTree.appendRow H y h) A k) :
    ∃ (h : AM H y.terminalCut 1) (V : FatTree H),
      ReviewTraceGood H c n O y h ∧ Reduces H V U ∧
      ExtendsStem H (FiniteFatTree.appendRow H y h) V ∧
      ReviewTraceLarge H c n O (FiniteFatTree.appendRow H y h) V := by
  let G := FixedTraceGoodRows H c n y hn hsrc O
  let P : PairContinuation H y := fun h =>
    FixedTraceGoodRows H c n (FiniteFatTree.appendRow H y h)
      (by rw [FiniteFatTree.appendRow_height]; omega)
      (traceSource_eq_after_append H c n y hn hsrc h) O
  have hdense : ∀ A : FatTree H, Reduces H A U → ExtendsStem H y A →
      ∃ h, h ∈ G ∧ ∃ k, k ∈ P h ∧
        OneBlockOccurs H (FiniteFatTree.appendRow H y h) A k := by
    intro A hAU hyA
    obtain ⟨h, k, hpair, hk⟩ := hpairs A hAU hyA
    exact ⟨h, hpair.1, k,
      (fixedTraceUpdateGood_iff H c n y hn hsrc O h k).1 hpair.2, hk⟩
  obtain ⟨h, hh, V, hVU, hyhV, hnext⟩ :=
    persistentAcceptedPair_of_dense_pairs H y U hyU G P hdense
  refine ⟨h, V, ⟨hn, hsrc, hh⟩, hVU, hyhV, ?_⟩
  exact ⟨by rw [FiniteFatTree.appendRow_height]; omega,
    traceSource_eq_after_append H c n y hn hsrc h, hnext⟩

/-- The local good-pair principle implies persistence for the entire updated
trace family. -/
theorem review_trace_persistence
    (hp : ReviewGoodPairPrinciple H)
    (c n : Nat) (O : Set (AM H c 1))
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U) (hlarge : ReviewTraceLarge H c n O y U) :
    ∃ (h : AM H y.terminalCut 1) (V : FatTree H),
      ReviewTraceGood H c n O y h ∧ Reduces H V U ∧
      ExtendsStem H (FiniteFatTree.appendRow H y h) V ∧
      ReviewTraceLarge H c n O (FiniteFatTree.appendRow H y h) V := by
  rcases hlarge with ⟨hn, hsrc, hrows⟩
  apply review_trace_persistence_core H c n O y U hn hsrc hyU hrows
  intro A hAU hyA
  exact hp c n y hn hsrc O A hyA
    (oneBlockLarge_mono H hrows hAU hyA)

/-- Generic fixed-source fusion.  All combinatorics are isolated in
`hpersist`; this theorem only performs the exact-depth fusion and transports
the finite-prefix invariant to its limit. -/
theorem review_all_trace_fusion_of_persistence
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (O : Set (AM H y.terminalCut 1)) (hlarge : OneBlockLarge H y U O)
    (hpersist : ∀ (z : FiniteFatTree H) (A : FatTree H),
      ExtendsStem H y A →
      ExtendsStem H z A →
      ReviewTraceLarge H y.terminalCut y.height O z A →
      ∃ (h : AM H z.terminalCut 1) (V : FatTree H),
        ReviewTraceGood H y.terminalCut y.height O z h ∧ Reduces H V A ∧
        ExtendsStem H (FiniteFatTree.appendRow H z h) V ∧
        ReviewTraceLarge H y.terminalCut y.height O
          (FiniteFatTree.appendRow H z h) V) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ∀ m : Nat, y.height ≤ m →
        ReviewStepGood H y.terminalCut y.height O
          (V.initialSegment H (m + 1)) := by
  classical
  let State (i : Nat) := {A : FatTree H //
    Reduces H A U ∧ ExtendsStem H y A ∧
      ReviewTraceLarge H y.terminalCut y.height O
        (A.initialSegment H (y.height + i)) A}
  have hbase : ReviewTraceLarge H y.terminalCut y.height O
      (U.initialSegment H y.height) U := by
    rw [initialSegment_eq_of_extendsStem H hyU]
    refine ⟨le_rfl, baseTraceSource H y, ?_⟩
    rwa [fixedTraceGoodRows_base H y O]
  let start : State 0 := ⟨U, reduces_refl H U, hyU, by
    simpa only [Nat.add_zero] using hbase⟩
  have hstep : ∀ i : Nat, ∀ A : State i, ∃ B : State (i + 1),
      InDepthCone H (y.height + i) A.1 B.1 ∧
      ReviewStepGood H y.terminalCut y.height O
        (B.1.initialSegment H (y.height + i + 1)) := by
    intro i A
    let z := A.1.initialSegment H (y.height + i)
    obtain ⟨h, V, hgood, hVA, hzV, hnext⟩ :=
      hpersist z A.1 A.2.2.1
        (initialSegment_extendsStem H A.1 (y.height + i)) A.2.2.2
    have hcone : InDepthCone H (y.height + i) A.1 V :=
      ⟨hVA, extendsStem_of_appendRow H hzV⟩
    have hyV : ExtendsStem H y V :=
      extendsStem_of_depthCone H A.2.2.1 hcone (by omega)
    have heq : V.initialSegment H (y.height + i + 1) =
        FiniteFatTree.appendRow H z h :=
      initialSegment_eq_of_extendsStem H hzV
    have hnext' : ReviewTraceLarge H y.terminalCut y.height O
        (V.initialSegment H (y.height + (i + 1))) V := by
      rw [show y.height + (i + 1) = y.height + i + 1 by omega, heq]
      exact hnext
    exact ⟨⟨V, reduces_trans H hVA A.2.1, hyV, hnext'⟩,
      hcone, z, h, heq, hgood⟩
  choose next hnext hgood using hstep
  let Y : (i : Nat) → State i :=
    fun i => Nat.rec (motive := fun i => State i) start (fun i A => next i A) i
  have hYstep (i : Nat) :
      InDepthCone H (y.height + i) (Y i).1 (Y (i + 1)).1 := hnext i (Y i)
  have hYfusion : (approximationSystem H).IsFusionFrom y.height
      (fun i => (Y i).1) := by
    intro i
    exact (mem_levelNeighborhood_iff_depthCone H (y.height + i)
      (Y i).1 (Y (i + 1)).1).2 (hYstep i)
  obtain ⟨V, hV⟩ := (fusionComplete H).exists_limit hYfusion
  have hVcone (i : Nat) : InDepthCone H (y.height + i) (Y i).1 V :=
    (mem_levelNeighborhood_iff_depthCone H (y.height + i) (Y i).1 V).1 (hV i)
  refine ⟨V, reduces_trans H (hVcone 0).1 (Y 0).2.1,
    extendsStem_of_depthCone H (Y 0).2.2.1 (hVcone 0) (by omega), ?_⟩
  intro m hm
  let i := m - y.height
  have hid : y.height + i = m := by
    dsimp [i]
    omega
  have hprefix : V.initialSegment H (y.height + (i + 1)) =
      (Y (i + 1)).1.initialSegment H (y.height + (i + 1)) :=
    initialSegment_eq_of_extendsStem H (hVcone (i + 1)).2
  have htarget : y.height + (i + 1) = m + 1 := by omega
  have hselected : ReviewStepGood H y.terminalCut y.height O
      ((Y (i + 1)).1.initialSegment H (y.height + (i + 1))) :=
    hgood i (Y i)
  have hlimit : ReviewStepGood H y.terminalCut y.height O
      (V.initialSegment H (y.height + (i + 1))) :=
    (congrArg (ReviewStepGood H y.terminalCut y.height O) hprefix).mpr hselected
  have hdepth : V.initialSegment H (y.height + (i + 1)) =
      V.initialSegment H (m + 1) :=
    congrArg (fun d => V.initialSegment H d) htarget
  exact (congrArg (ReviewStepGood H y.terminalCut y.height O) hdepth).mp hlimit

/-- Construct the fixed-source fusion from the abstract good-pair principle. -/
theorem review_all_trace_fusion
    (hp : ReviewGoodPairPrinciple H)
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (O : Set (AM H y.terminalCut 1)) (hlarge : OneBlockLarge H y U O) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ∀ m : Nat, y.height ≤ m →
        ReviewStepGood H y.terminalCut y.height O
          (V.initialSegment H (m + 1)) := by
  apply review_all_trace_fusion_of_persistence H y U hyU O hlarge
  intro z A _ hzA hzlarge
  exact review_trace_persistence H hp y.terminalCut y.height O z A hzA hzlarge

/-- Transport the good-row statement across equality of finite prefixes,
using heterogeneous equality only for the indexed row itself. -/
theorem review_goodRows_transport
    (c n : Nat) (O : Set (AM H c 1))
    {y z : FiniteFatTree H} (hyz : y = z)
    {h : AM H y.terminalCut 1} {k : AM H z.terminalCut 1}
    (hhk : HEq h k)
    (hn : n ≤ y.height) (hn' : n ≤ z.height)
    (hs : FiniteFatTree.traceSourceCut H y n hn = c)
    (hs' : FiniteFatTree.traceSourceCut H z n hn' = c)
    (hg : h ∈ FixedTraceGoodRows H c n y hn hs O) :
    k ∈ FixedTraceGoodRows H c n z hn' hs' O := by
  cases hyz
  cases eq_of_heq hhk
  exact hg

/-- The finite-prefix invariant gives the actual ambient row invariant
needed by last-block coverage. -/
theorem review_good_row_of_good_prefix
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (O : Set (AM H y.terminalCut 1)) (m : Nat) (hym : y.height ≤ m)
    (hg : ReviewStepGood H y.terminalCut y.height O
      (U.initialSegment H (m + 1))) :
    U.row m ∈ FixedTraceGoodRows H y.terminalCut y.height
      (U.initialSegment H m) hym
      (initialSegment_traceSource_of_extendsStem H y U hyU m hym) O := by
  rcases hg with ⟨z, h, heq, hn, hs, hgood⟩
  have hzheight : z.height = m := by
    have ht := congrArg FiniteFatTree.height heq
    change m + 1 = z.height + 1 at ht
    omega
  have hzU : ExtendsStem H (FiniteFatTree.appendRow H z h) U := by
    apply extendsStem_of_initialSegment_eq H
    simpa only [FiniteFatTree.appendRow_height, hzheight] using heq
  have hzold := extendsStem_of_appendRow H hzU
  have hz : U.initialSegment H m = z := by
    simpa only [hzheight] using initialSegment_eq_of_extendsStem H hzold
  have hr : HEq h (U.row m) := by
    have hr0 := (hzU.2 (Fin.last z.height)).trans
      (FiniteFatTree.appendRow_row_last H z h)
    have hrow_congr : ∀ {a b : Nat}, a = b → HEq (U.row a) (U.row b) := by
      intro a b hab
      cases hab
      rfl
    exact hr0.symm.trans (hrow_congr hzheight)
  exact review_goodRows_transport H y.terminalCut y.height O hz.symm hr
    hn hym hs (initialSegment_traceSource_of_extendsStem H y U hyU m hym) hgood

/-- The global large-set theorem in the review: every large O has a
homogeneous stem-preserving reduction. Only the local good-pair theorem
remains as a hypothesis, and the original source cut is positive. -/
theorem review_large_set_homogeneous
    (hp : ReviewGoodPairPrinciple H)
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (hpos : 0 < y.terminalCut)
    (O : Set (AM H y.terminalCut 1)) (hlarge : OneBlockLarge H y U O) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ∀ g, OneBlockOccurs H y V g → g ∈ O := by
  obtain ⟨V, hVU, hyV, hgood⟩ := review_all_trace_fusion H hp y U hyU O hlarge
  refine ⟨V, hVU, hyV, ?_⟩
  exact oneBlock_mem_of_all_fixedTraceGoodRows H y V hyV hpos O
    (fun m hm => review_good_row_of_good_prefix H y V hyV O m hm (hgood m hm))

/-- Positive-source-cut A4 from the review's local two-block lemma.
The alternative is immediate avoidance when O is not large. -/
theorem review_fixedStemPigeonhole_positive
    (hp : ReviewGoodPairPrinciple H)
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (hpos : 0 < y.terminalCut) (O : Set (AM H y.terminalCut 1)) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ((∀ g, OneBlockOccurs H y V g → g ∈ O) ∨
       (∀ g, OneBlockOccurs H y V g → g ∉ O)) := by
  classical
  by_cases hlarge : OneBlockLarge H y U O
  · obtain ⟨V, hVU, hyV, hgood⟩ := review_large_set_homogeneous H hp y U hyU hpos O hlarge
    exact ⟨V, hVU, hyV, Or.inl hgood⟩
  · obtain ⟨V, hVU, hyV, havoid⟩ := exists_avoiding_refinement_of_not_large H hlarge
    exact ⟨V, hVU, hyV, Or.inr havoid⟩

end SuccessorTree.SMTree.FatTree
