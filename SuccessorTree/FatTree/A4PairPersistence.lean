import SuccessorTree.FatTree.A4Coverage
import SuccessorTree.FatTree.A4Persistence
import SuccessorTree.FatTree.A4TypedBridge

/-!
# The review proof's pair-persistence lemma

This is the Baumgartner step behind `lem:fixlevel` and
`lem:trace-persistence`. Instead of enumerating heads globally and then
proving that the active depths tend to infinity, process the finite set of
heads at each currently protected depth. A3 lifts an avoidance below a
chosen head back to that depth of the ambient tree. Closedness supplies the
fusion limit. No A4, Hales--Jewett, EA, or inverse-closure assumption is used.

The acceptance set for the second block may depend on the first block.
Consequently this applies to the review's exact-trace update, not just to
lines following the immediately preceding selected head.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

private theorem pairCone_refl (d : Nat) (U : FatTree H) :
    InDepthCone H d U U :=
  ⟨reduces_refl H U, initialSegment_extendsStem H U d⟩

private theorem pairCone_trans {d : Nat} {U V W : FatTree H}
    (hVU : InDepthCone H d U V) (hWV : InDepthCone H d V W) :
    InDepthCone H d U W := by
  refine ⟨reduces_trans H hWV.1 hVU.1, ?_⟩
  have heq : V.initialSegment H d = U.initialSegment H d :=
    initialSegment_eq_of_extendsStem H hVU.2
  simpa only [heq] using hWV.2

/-- A geometric two-block occurrence includes its first block. -/
theorem oneBlockOccurs_of_pair
    (y : FiniteFatTree H) (U : FatTree H)
    (g : AM H y.terminalCut 1)
    (k : AM H (FiniteFatTree.appendRow H y g).terminalCut 1)
    (hk : OneBlockOccurs H (FiniteFatTree.appendRow H y g) U k) :
    OneBlockOccurs H y U g := by
  rcases hk with ⟨d, hd⟩
  obtain ⟨W, hW⟩ := a3_one_nonempty H hd (pairCone_refl H d U)
  exact exists_stemAt_of_neighborhood H
    ⟨hW.1, extendsStem_of_appendRow H hW.2⟩

/-- Appending a row does not identify different row approximations. -/
theorem appendRow_injective (y : FiniteFatTree H) :
    Function.Injective (FiniteFatTree.appendRow H y) := by
  intro g k heq
  have hr := FiniteFatTree.row_heq_of_eq H heq (Fin.last y.height)
  have hg := FiniteFatTree.appendRow_row_last H y g
  have hk := FiniteFatTree.appendRow_row_last H y k
  exact eq_of_heq (hg.symm.trans (hr.trans hk))

/-- Only finitely many heads can end at a fixed ambient cut. -/
theorem headsAtDepth_finite (y : FiniteFatTree H) (U : FatTree H) (d : Nat) :
    {g : AM H y.terminalCut 1 |
      StemAt H (FiniteFatTree.appendRow H y g) U d}.Finite := by
  exact (FiniteFatTree.leFin_lower_finite H (U.initialSegment H d)).preimage
    (appendRow_injective H y).injOn

/-- A dependent family of accepted second blocks. -/
abbrev PairContinuation (y : FiniteFatTree H) :=
  (g : AM H y.terminalCut 1) →
    Set (AM H (FiniteFatTree.appendRow H y g).terminalCut 1)

/-- No accepted continuation of this head remains in the ambient tree. -/
def AvoidsAcceptedPair (y : FiniteFatTree H) (P : PairContinuation H y)
    (U : FatTree H) (g : AM H y.terminalCut 1) : Prop :=
  ∀ k, OneBlockOccurs H (FiniteFatTree.appendRow H y g) U k → k ∉ P g

theorem avoidsAcceptedPair_mono
    {y : FiniteFatTree H} {P : PairContinuation H y}
    {U V : FatTree H} {g : AM H y.terminalCut 1}
    (h : AvoidsAcceptedPair H y P U g) (hVU : Reduces H V U) :
    AvoidsAcceptedPair H y P V g := by
  intro k hk
  exact h k (oneBlockOccurs_of_reduces H hk hVU)

/-- A successful head has a large accepted continuation below a literal
realization of that head. -/
def HasPersistentAcceptedPair (y : FiniteFatTree H) (U : FatTree H)
    (O : Set (AM H y.terminalCut 1)) (P : PairContinuation H y) : Prop :=
  ∃ g, g ∈ O ∧ ∃ V : FatTree H,
    Reduces H V U ∧ ExtendsStem H (FiniteFatTree.appendRow H y g) V ∧
      OneBlockLarge H (FiniteFatTree.appendRow H y g) V (P g)

/-- A3 lifts avoidance below a head to an ambient refinement preserving the
entire prefix ending at that head's original depth. -/
theorem eliminate_accepted_pair_at_depth
    {y : FiniteFatTree H} {U A : FatTree H}
    {O : Set (AM H y.terminalCut 1)} {P : PairContinuation H y}
    (hbad : ¬ HasPersistentAcceptedPair H y U O P)
    (hAU : Reduces H A U)
    (g : AM H y.terminalCut 1) (hgO : g ∈ O)
    (d : Nat) (hgA : StemAt H (FiniteFatTree.appendRow H y g) A d) :
    ∃ B : FatTree H, InDepthCone H d A B ∧
      AvoidsAcceptedPair H y P B g := by
  let s := FiniteFatTree.appendRow H y g
  obtain ⟨V, hV⟩ := a3_one_nonempty H hgA (pairCone_refl H d A)
  have hnot : ¬ OneBlockLarge H s V (P g) := by
    intro hlarge
    exact hbad ⟨g, hgO, V, reduces_trans H hV.1 hAU, hV.2, hlarge⟩
  obtain ⟨W, hWV, hsW, havoid⟩ :=
    exists_avoiding_refinement_of_not_large H hnot
  have hWA : Reduces H W A := reduces_trans H hWV hV.1
  obtain ⟨e, B, hsA, hBA, _, hsub⟩ := a3_two_amalgamation H hWA
    ⟨W, reduces_refl H W, hsW⟩
  have hed : e = d := stemAt_unique H hsA hgA
  subst e
  refine ⟨B, hBA, ?_⟩
  intro k hk hkP
  rcases hk with ⟨l, hl⟩
  obtain ⟨Z, hZ⟩ := a3_one_nonempty H hl (pairCone_refl H l B)
  have hZs : InNeighborhood H s B Z :=
    ⟨hZ.1, extendsStem_of_appendRow H hZ.2⟩
  have hZW := hsub Z hZs
  have hkZ : OneBlockOccurs H s Z k := by
    refine ⟨(FiniteFatTree.appendRow H s k).height, ?_⟩
    exact leFin_initialSegment_of_extendsStem H hZ.2
  exact havoid k (oneBlockOccurs_of_reduces H hkZ hZW.1) hkP

/-- Eliminate a finite batch without disturbing its protected depth. -/
theorem eliminate_accepted_pair_batch
    {y : FiniteFatTree H} {U A : FatTree H}
    {O : Set (AM H y.terminalCut 1)} {P : PairContinuation H y}
    (hbad : ¬ HasPersistentAcceptedPair H y U O P)
    (hAU : Reduces H A U) (d : Nat)
    (F : Finset (AM H y.terminalCut 1))
    (hF : ∀ g ∈ F, StemAt H (FiniteFatTree.appendRow H y g) A d) :
    ∃ B : FatTree H, InDepthCone H d A B ∧
      ∀ g ∈ F, g ∈ O → AvoidsAcceptedPair H y P B g := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨A, pairCone_refl H d A, by simp⟩
  | @insert g F hgF ih =>
      intro hF
      obtain ⟨V, hVA, hclean⟩ := ih (by
        intro k hk
        exact hF k (Finset.mem_insert_of_mem hk))
      by_cases hgO : g ∈ O
      · have hgV := stemAt_of_depthCone H (hF g (Finset.mem_insert_self _ _)) hVA
        obtain ⟨B, hBV, hgclean⟩ := eliminate_accepted_pair_at_depth H hbad
          (reduces_trans H hVA.1 hAU) g hgO d hgV
        refine ⟨B, pairCone_trans H hVA hBV, ?_⟩
        intro k hk hkO
        rcases Finset.mem_insert.mp hk with rfl | hkF
        · exact hgclean
        · exact avoidsAcceptedPair_mono H (hclean k hkF hkO) hBV.1
      · refine ⟨V, hVA, ?_⟩
        intro k hk hkO
        rcases Finset.mem_insert.mp hk with rfl | hkF
        · exact False.elim (hgO hkO)
        · exact hclean k hkF hkO

/-- The whole finite batch at the current cut can be processed at once. -/
theorem eliminate_all_accepted_pairs_at_depth
    {y : FiniteFatTree H} {U A : FatTree H}
    {O : Set (AM H y.terminalCut 1)} {P : PairContinuation H y}
    (hbad : ¬ HasPersistentAcceptedPair H y U O P)
    (hAU : Reduces H A U) (d : Nat) :
    ∃ B : FatTree H, InDepthCone H d A B ∧
      ∀ g, g ∈ O → StemAt H (FiniteFatTree.appendRow H y g) A d →
        AvoidsAcceptedPair H y P B g := by
  classical
  let hf := headsAtDepth_finite H y A d
  obtain ⟨B, hBA, hclean⟩ := eliminate_accepted_pair_batch H hbad hAU d
    hf.toFinset (by intro g hg; exact hf.mem_toFinset.mp hg)
  exact ⟨B, hBA, fun g hg hd => hclean g (hf.mem_toFinset.mpr hd) hg⟩

/-- The review proof's persistence step, with arbitrary dependent accepted
continuations. Its only local hypothesis supplies a good pair in each
stem-preserving refinement; the passage from pairs to a large continuation
is proved here by A3 and metric fusion, not assumed. -/
theorem persistentAcceptedPair_of_dense_pairs
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (O : Set (AM H y.terminalCut 1)) (P : PairContinuation H y)
    (hpairs : ∀ A : FatTree H, Reduces H A U → ExtendsStem H y A →
      ∃ g, g ∈ O ∧ ∃ k, k ∈ P g ∧
        OneBlockOccurs H (FiniteFatTree.appendRow H y g) A k) :
    HasPersistentAcceptedPair H y U O P := by
  classical
  by_contra hbad
  have hstep : ∀ i : Nat, ∀ A : StemRefinement H y U,
      ∃ B : StemRefinement H y U,
        InDepthCone H (y.height + i) A.1 B.1 ∧
        ∀ g, g ∈ O →
          StemAt H (FiniteFatTree.appendRow H y g) A.1 (y.height + i) →
          AvoidsAcceptedPair H y P B.1 g := by
    intro i A
    obtain ⟨B, hBA, hclean⟩ :=
      eliminate_all_accepted_pairs_at_depth H hbad A.2.1 (y.height + i)
    exact ⟨⟨B, reduces_trans H hBA.1 A.2.1,
      extendsStem_of_depthCone H A.2.2 hBA (by omega)⟩, hBA, hclean⟩
  choose next hnext hclean using hstep
  let Y : Nat → StemRefinement H y U :=
    fun i => Nat.rec (⟨U, reduces_refl H U, hyU⟩ : StemRefinement H y U)
      (fun k A => next k A) i
  have hYstep (i : Nat) :
      InDepthCone H (y.height + i) (Y i).1 (Y (i + 1)).1 :=
    hnext i (Y i)
  have hYfusion : (approximationSystem H).IsFusionFrom y.height
      (fun i => (Y i).1) := by
    intro i
    exact (mem_levelNeighborhood_iff_depthCone H (y.height + i)
      (Y i).1 (Y (i + 1)).1).2 (hYstep i)
  obtain ⟨W, hW⟩ := (fusionComplete H).exists_limit hYfusion
  have hWcone (i : Nat) : InDepthCone H (y.height + i) (Y i).1 W :=
    (mem_levelNeighborhood_iff_depthCone H (y.height + i) (Y i).1 W).1 (hW i)
  have hWU : Reduces H W U := reduces_trans H (hWcone 0).1 (Y 0).2.1
  have hyW : ExtendsStem H y W :=
    extendsStem_of_depthCone H (Y 0).2.2 (hWcone 0) (by omega)
  obtain ⟨g, hgO, k, hkP, hkW⟩ := hpairs W hWU hyW
  obtain ⟨d, hgd⟩ := oneBlockOccurs_of_pair H y W g k hkW
  have hnd : y.height < d := height_lt_of_appended_stemAt H y W g d hgd
  let i := d - y.height
  have hid : y.height + i = d := by dsimp [i]; omega
  have hcone : InDepthCone H d (Y i).1 W := by
    simpa only [hid] using hWcone i
  have heq : W.initialSegment H d = (Y i).1.initialSegment H d :=
    initialSegment_eq_of_extendsStem H hcone.2
  have hgYi : StemAt H (FiniteFatTree.appendRow H y g) (Y i).1 (y.height + i) := by
    rw [hid]
    unfold StemAt at hgd ⊢
    rwa [heq] at hgd
  have havoid : AvoidsAcceptedPair H y P (Y (i + 1)).1 g :=
    hclean i (Y i) g hgO hgYi
  exact havoid k (oneBlockOccurs_of_reduces H hkW (hWcone (i + 1)).1) hkP

end SuccessorTree.SMTree.FatTree
