import SuccessorTree.FatTree.A4ReviewFusion
import SuccessorTree.FatTree.A4ReviewGoodPair
import SuccessorTree.FatTree.A4Root

/-!
# Source-letter completion of the alternative A4 fusion

The review proof only needs a one-level letter at the original source cut.
At later protected cuts the letter is transported by equality or supplied by
M3 duplication.  This removes the artificial positive-cut restriction from
the all-trace fusion.  If no source letter exists, the source cut is zero and
all root rows are equal, so homogeneity is immediate.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- The checked local good-pair theorem gives persistence directly when a
source letter is available; no global good-pair principle is assumed. -/
theorem review_trace_persistence_of_sourceLetter
    (c n : Nat) (O : Set (AM H c 1))
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (hlarge : ReviewTraceLarge H c n O y U) :
    ∃ (h : AM H y.terminalCut 1) (V : FatTree H),
      ReviewTraceGood H c n O y h ∧ Reduces H V U ∧
      ExtendsStem H (FiniteFatTree.appendRow H y h) V ∧
      ReviewTraceLarge H c n O (FiniteFatTree.appendRow H y h) V := by
  rcases hlarge with ⟨hn, hsrc, hlarge⟩
  let G := FixedTraceGoodRows H c n y hn hsrc O
  let P : PairContinuation H y := fun h =>
    FixedTraceGoodRows H c n (FiniteFatTree.appendRow H y h)
      (by rw [FiniteFatTree.appendRow_height]; omega)
      (traceSource_eq_after_append H c n y hn hsrc h) O
  have hdense : ∀ A : FatTree H, Reduces H A U → ExtendsStem H y A →
      ∃ h, h ∈ G ∧ ∃ k, k ∈ P h ∧
        OneBlockOccurs H (FiniteFatTree.appendRow H y h) A k := by
    intro A hAU hyA
    obtain ⟨h, k, hpair, hk⟩ :=
      review_goodPair_of_sourceLetter H c n y hn hsrc O A hyA Esource
        (oneBlockLarge_mono H hlarge hAU hyA)
    exact ⟨h, hpair.1, k,
      (fixedTraceUpdateGood_iff H c n y hn hsrc O h k).1 hpair.2, hk⟩
  obtain ⟨h, hh, V, hVU, hyhV, hnext⟩ :=
    persistentAcceptedPair_of_dense_pairs H y U hyU G P hdense
  refine ⟨h, V, ⟨hn, hsrc, hh⟩, hVU, hyhV, ?_⟩
  exact ⟨by rw [FiniteFatTree.appendRow_height]; omega,
    traceSource_eq_after_append H c n y hn hsrc h, hnext⟩

/-- Fixed-source all-trace fusion from an explicit source letter.  The same
original letter is carried to each later finite prefix before applying the
local good-pair theorem. -/
theorem review_all_trace_fusion_of_sourceLetter
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (O : Set (AM H y.terminalCut 1)) (hlarge : OneBlockLarge H y U O) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ∀ m : Nat, y.height ≤ m →
        ReviewStepGood H y.terminalCut y.height O (V.initialSegment H (m + 1)) := by
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
    have hsourceLe : y.terminalCut ≤ z.terminalCut := by
      dsimp [z]
      calc
        y.terminalCut = A.1.cut y.height :=
          (terminalCut_eq_of_extendsStem H A.2.2.1).symm
        _ ≤ A.1.cut (y.height + i) :=
          (A.1.cut_strictMono H).monotone (by omega)
        _ = (A.1.initialSegment H (y.height + i)).terminalCut := rfl
    let Ez : OneLevelLetter H z.terminalCut :=
      reviewLaterSourceLetter H y.terminalCut z.terminalCut hsourceLe Esource
    obtain ⟨h, V, hgood, hVA, hzV, hnext⟩ :=
      review_trace_persistence_of_sourceLetter H
        y.terminalCut y.height O z A.1
        (initialSegment_extendsStem H A.1 (y.height + i)) Ez A.2.2.2
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
  have hid : y.height + i = m := by dsimp [i]; omega
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

/-- Every large set is homogeneous below a source-letter stem. -/
theorem review_large_set_homogeneous_of_sourceLetter
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (O : Set (AM H y.terminalCut 1)) (hlarge : OneBlockLarge H y U O) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ∀ g, OneBlockOccurs H y V g → g ∈ O := by
  obtain ⟨V, hVU, hyV, hgood⟩ :=
    review_all_trace_fusion_of_sourceLetter H y U hyU Esource O hlarge
  refine ⟨V, hVU, hyV, ?_⟩
  exact oneBlock_mem_of_all_fixedTraceGoodRows_of_sourceLetter H y V hyV
    Esource O
    (fun m hm => review_good_row_of_good_prefix H y V hyV O m hm (hgood m hm))

/-- Geometric fixed-stem pigeonhole theorem whenever the source cut has a
one-level letter. -/
theorem review_fixedStemPigeonhole_of_sourceLetter
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (O : Set (AM H y.terminalCut 1)) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ((∀ g, OneBlockOccurs H y V g → g ∈ O) ∨
       (∀ g, OneBlockOccurs H y V g → g ∉ O)) := by
  classical
  by_cases hlarge : OneBlockLarge H y U O
  · obtain ⟨V, hVU, hyV, hgood⟩ :=
      review_large_set_homogeneous_of_sourceLetter H y U hyU Esource O hlarge
    exact ⟨V, hVU, hyV, Or.inl hgood⟩
  · obtain ⟨V, hVU, hyV, havoid⟩ :=
      exists_avoiding_refinement_of_not_large H hlarge
    exact ⟨V, hVU, hyV, Or.inr havoid⟩

/-- If a source cut has no one-level letter, then M3 forces that cut to
be zero and every row based there is the identity root row. -/
theorem review_rows_eq_of_no_sourceLetter
    (c : Nat) (hno : ¬ Nonempty (OneLevelLetter H c))
    (g k : AM H c 1) : g = k := by
  have hc : c = 0 := by
    by_contra hne
    have hpos : 0 < c := Nat.pos_of_ne_zero hne
    exact hno ⟨duplicateHistoryLetter H 0 c hpos⟩
  subst c
  exact (H.rootRow_eq_id1_of_no_rootLetter hno g).trans
    (H.rootRow_eq_id1_of_no_rootLetter hno k).symm

/-- Full geometric fixed-stem pigeonhole theorem.  If there is no source
letter, M3 forces the source cut to be zero and every root row is the same;
then the original ambient tree is already homogeneous. -/
theorem review_fixedStemPigeonhole
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (O : Set (AM H y.terminalCut 1)) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ((∀ g, OneBlockOccurs H y V g → g ∈ O) ∨
       (∀ g, OneBlockOccurs H y V g → g ∉ O)) := by
  classical
  by_cases hletter : Nonempty (OneLevelLetter H y.terminalCut)
  · rcases hletter with ⟨Esource⟩
    exact review_fixedStemPigeonhole_of_sourceLetter H y U hyU Esource O
  · have hrows : ∀ g k : AM H y.terminalCut 1, g = k :=
      review_rows_eq_of_no_sourceLetter H y.terminalCut hletter
    let g0 : AM H y.terminalCut 1 := ambientNextRow H y U hyU
    refine ⟨U, reduces_refl H U, hyU, ?_⟩
    by_cases hg0 : g0 ∈ O
    · left
      intro g _
      simpa only [hrows g g0] using hg0
    · right
      intro g _ hgO
      apply hg0
      simpa only [hrows g g0] using hgO

end SuccessorTree.SMTree.FatTree
