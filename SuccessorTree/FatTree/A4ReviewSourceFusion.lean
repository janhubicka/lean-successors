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

/-- The checked source-letter good-pair theorem feeds the common
persistence core directly; no global good-pair principle is assumed. -/
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
  rcases hlarge with ⟨hn, hsrc, hrows⟩
  apply review_trace_persistence_core H c n O y U hn hsrc hyU
  intro A hAU hyA
  exact review_goodPair_of_sourceLetter H c n y hn hsrc O A hyA Esource
    (oneBlockLarge_mono H hrows hAU hyA)

/-- Fixed-source all-trace fusion from an explicit source letter.  The
generic fusion engine is reused; the only extra work is transporting the
original source letter to the current terminal cut. -/
theorem review_all_trace_fusion_of_sourceLetter
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (O : Set (AM H y.terminalCut 1)) (hlarge : OneBlockLarge H y U O) :
    ∃ V : FatTree H, Reduces H V U ∧ ExtendsStem H y V ∧
      ∀ m : Nat, y.height ≤ m →
        ReviewStepGood H y.terminalCut y.height O
          (V.initialSegment H (m + 1)) := by
  apply review_all_trace_fusion_of_persistence H y U hyU O hlarge
  intro z A hyA hzA hzlarge
  rcases hzlarge with ⟨hn, hsrc, hrows⟩
  have hsourceLe : y.terminalCut ≤ z.terminalCut := by
    calc
      y.terminalCut = A.cut y.height :=
        (terminalCut_eq_of_extendsStem H hyA).symm
      _ ≤ A.cut z.height :=
        (A.cut_strictMono H).monotone hn
      _ = z.terminalCut :=
        terminalCut_eq_of_extendsStem H hzA
  let Ez : OneLevelLetter H z.terminalCut :=
    reviewLaterSourceLetter H y.terminalCut z.terminalCut hsourceLe Esource
  exact review_trace_persistence_of_sourceLetter H
    y.terminalCut y.height O z A hzA Ez ⟨hn, hsrc, hrows⟩

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
theorem fatTreeFixedStemPigeonhole
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
