import SuccessorTree.FatTree.A4ReviewWitness

/-!
# The large-set good-pair lemma of the alternative A4 proof

The local simultaneous fan line is applied to every composite p q, where q
is an original trace and p ranges over the finite bridges to the persistent
depth. The accepted head is then selected by exact-depth persistence.
Canonical transport of raw fans proves that its common tail is good after
EVERY raw trace update. This file does not assume the good-pair principle.

The geometric factorisation only needs an immediate successor on the source
cut.  An explicit source letter supplies this also at cut zero; the no-letter
root case is handled separately in the final theorem.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Carry a one-level source letter to any later cut. Equality merely
transports the dependent index; strict growth uses the M3 duplicate. -/
noncomputable def reviewLaterSourceLetter
    (c d : Nat) (hcd : c ≤ d) (E : OneLevelLetter H c) :
    OneLevelLetter H d := by
  by_cases heq : c = d
  · exact heq ▸ E
  · exact duplicateHistoryLetter H c d (lt_of_le_of_ne hcd heq)

/-- Source transport for an exact trace. -/
noncomputable def reviewCastExactSource {c c' d : Nat}
    (hc : c = c') (p : AMExact H c d) : AMExact H c' d :=
  ⟨FiniteFatTree.castTraceRow H hc p.1, by
    change (FiniteFatTree.castTraceRow H hc p.1).rowEndLevel H = d
    calc
      (FiniteFatTree.castTraceRow H hc p.1).rowEndLevel H =
          p.1.rowEndLevel H :=
        FiniteFatTree.castTraceRow_rowEndLevel H hc p.1
      _ = d := p.2⟩

/-- Source transport commutes with substitution. -/
theorem review_composeAcross_cast_source {c c' d : Nat}
    (hc : c = c') (p : AMExact H c d) (h : AM H d 1) :
    FiniteFatTree.castTraceRow H hc (H.composeAcross p h) =
      H.composeAcross (reviewCastExactSource H hc p) h := by
  cases hc
  rfl

/-- A good pair for any nonempty finite family of exact traces from a prefix
whose source cut carries a one-level letter.  Neither A4 nor a global
good-pair principle is assumed. -/
theorem review_goodPair_finite_family_of_sourceLetter
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (trace : C → AMExact H c y.terminalCut) (O : Set (AM H c 1))
    (hlarge : OneBlockLarge H y U
      {g | ∀ j : C, H.composeAcross (trace j) g ∈ O}) :
    ∃ (g : AM H y.terminalCut 1)
      (k : AM H (FiniteFatTree.appendRow H y g).terminalCut 1),
      (∀ j : C, H.composeAcross (trace j) g ∈ O) ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y g) U k ∧
      ∀ (j : C) (e : RawSuccessorFan H (trace j).1)
        (theta : AMExact H c (FiniteFatTree.appendRow H y g).terminalCut),
        (∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
          theta.1.representative H x.1 =
            H.canonicalExtension (g.representative H) y.terminalCut (e.toFun x).1) →
        H.composeAcross theta k ∈ O := by
  classical
  let G : Set (AM H y.terminalCut 1) :=
    {g | ∀ j : C, H.composeAcross (trace j) g ∈ O}
  obtain ⟨A, a, hAU, hyA, hya, hP⟩ := oneBlockLarge_exact_persistent_closed H hyU hlarge
  let R := FiniteFatTree.ExactTrace H (A.initialSegment H a) y.height hya
  letI : Fintype R := by
    dsimp [R]
    exact exactTraceFintype H (A.initialSegment H a) y.height hya
  letI : Nonempty R :=
    review_bridges_nonempty_of_sourceLetter H y A hyA Esource G a hya hP
  let bridge : R → AMExact H y.terminalCut (A.cut a) := reviewBridgeMap H y A hyA a hya
  let family : R × C → AM H c 1 := fun j => H.composeAcross (trace j.2) (bridge j.1).1
  have hend : ∀ j : R × C, (family j).rowEndLevel H = A.cut a := by
    intro j
    exact (review_composeAcross_end H (trace j.2) (bridge j.1).1).trans (bridge j.1).2
  have hsource_le : y.terminalCut ≤ A.cut a := by
    calc
      y.terminalCut = A.cut y.height :=
        (terminalCut_eq_of_extendsStem H hyA).symm
      _ ≤ A.cut a := (A.cut_strictMono H).monotone hya
  let Ecurrent : OneLevelLetter H (A.cut a) :=
    reviewLaterSourceLetter H y.terminalCut (A.cut a) hsource_le Esource
  let chi : AM H c 1 → Bool := fun f => decide (f ∈ O)
  obtain ⟨L⟩ := exists_reviewFanLine_of_sourceLetter H A a family hend Ecurrent chi
  obtain ⟨p, g, k, hgG, hfactor, hktail, hkA⟩ :=
    review_persistent_line_witness_of_sourceLetter H y A hyA Esource
      G a hya hP family hend chi L
  refine ⟨g, k, hgG, oneBlockOccurs_of_reduces H hkA hAU, ?_⟩
  intro j e theta hraw
  have hterminal : (FiniteFatTree.appendRow H y g).terminalCut = A.cut L.headDepth := by
    rw [FiniteFatTree.appendRow_terminalCut, hfactor, review_composeAcross_end]
    exact L.head_end
  let theta' : AMExact H c (A.cut L.headDepth) := ⟨theta.1, theta.2.trans hterminal⟩
  have hraw' : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
      theta.1.representative H x.1 =
        H.canonicalExtension ((H.composeAcross (bridge p) L.head).representative H)
          y.terminalCut (e.toFun x).1 := by
    intro x hx
    rw [← hfactor]
    exact hraw x hx
  have hcolour := reviewFanLine_factor_colour H L (trace j) (bridge p)
    (p, j) rfl e theta.1 theta'.2 hraw'
  have htransport : H.composeAcross theta k = H.composeAcross theta' L.tail :=
    eq_of_heq (review_composeAcross_heq H rfl hterminal HEq.rfl hktail)
  have hcolour' : chi (H.composeAcross theta k) = chi (H.composeAcross (trace j) g) := by
    rw [htransport]
    exact hcolour.trans (congrArg (fun h => chi (H.composeAcross (trace j) h)) hfactor.symm)
  have hright : chi (H.composeAcross (trace j) g) = true := by
    simp only [chi, decide_eq_true_eq]
    exact hgG j
  have hleft := hcolour'.trans hright
  simpa only [chi, decide_eq_true_eq] using hleft

/-- The finite-family good pair instantiated with ALL exact traces of the
current prefix. The empty trace family is handled directly, without asking
Hales--Jewett for a nonempty alphabet. -/
theorem review_goodPair_at_prefix_of_sourceLetter
    (n : Nat) (y : FiniteFatTree H) (hn : n ≤ y.height)
    (O : Set (AM H (FiniteFatTree.traceSourceCut H y n hn) 1))
    (U : FatTree H) (hyU : ExtendsStem H y U)
    (Esource : OneLevelLetter H y.terminalCut)
    (hlarge : OneBlockLarge H y U
      (FixedTraceGoodRows H (FiniteFatTree.traceSourceCut H y n hn) n y hn rfl O)) :
    ∃ h k,
      FixedTraceGoodPair H (FiniteFatTree.traceSourceCut H y n hn) n y hn rfl O h k ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y h) U k := by
  classical
  let c := FiniteFatTree.traceSourceCut H y n hn
  let C := FiniteFatTree.ExactTrace H y n hn
  by_cases hne : Nonempty C
  · letI : Fintype C := Fintype.ofFinite C
    letI : Nonempty C := hne
    let trace : C → AMExact H c y.terminalCut := exactTraceToAMExact H y n hn
    obtain ⟨g, k, hg, hk, hupdate⟩ :=
      review_goodPair_finite_family_of_sourceLetter H y U hyU Esource trace O hlarge
    refine ⟨g, k, ⟨hg, ?_⟩, hk⟩
    intro theta q hraw
    let hc := FiniteFatTree.traceSourceCut_appendRow H y g n hn
    let th := reviewCastExactSource H hc
      (exactTraceToAMExact H (FiniteFatTree.appendRow H y g) n
        (by rw [FiniteFatTree.appendRow_height]; omega) theta)
    obtain ⟨e, he⟩ := review_exists_fan_of_pointwise H q.1
      (H.canonicalExtension (g.representative H) y.terminalCut)
      (theta.1.representative H) hraw
    have hthraw : ∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
        th.1.representative H x.1 =
          H.canonicalExtension (g.representative H) y.terminalCut (e.toFun x).1 := by
      intro x hx
      simpa only [th, reviewCastExactSource, exactTraceToAMExact,
        FiniteFatTree.castTraceRow_representative] using he x hx
    have hgood := hupdate q e th hthraw
    let ptheta :=
      exactTraceToAMExact H (FiniteFatTree.appendRow H y g) n
        (by rw [FiniteFatTree.appendRow_height]; omega) theta
    have hcast :=
      review_composeAcross_cast_source H hc ptheta k
    have hmem :
        (FiniteFatTree.castTraceRow H hc (H.composeAcross ptheta k) ∈ O) =
          (H.composeAcross (reviewCastExactSource H hc ptheta) k ∈ O) :=
      congrArg (fun z => z ∈ O) hcast
    apply Eq.mpr hmem
    simpa only [th, ptheta] using hgood
  · let g := ambientNextRow H y U hyU
    let z := FiniteFatTree.appendRow H y g
    have hzU : ExtendsStem H z U := by
      apply extendsStem_of_initialSegment_eq H
      exact (appendRow_ambientNextRow H y U hyU).symm
    let k := ambientNextRow H z U hzU
    refine ⟨g, k, ⟨?_, ?_⟩, ambientNextRow_occurs H z U hzU⟩
    · intro q
      exact False.elim (hne ⟨q⟩)
    · intro theta q hraw
      exact False.elim (hne ⟨q⟩)

/-- Positive-cut compatibility wrapper for the finite-family lemma. -/
theorem review_goodPair_finite_family_positive
    {c : Nat} {C : Type w} [Fintype C] [Nonempty C]
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (hpos : 0 < y.terminalCut)
    (trace : C → AMExact H c y.terminalCut) (O : Set (AM H c 1))
    (hlarge : OneBlockLarge H y U
      {g | ∀ j : C, H.composeAcross (trace j) g ∈ O}) :
    ∃ (g : AM H y.terminalCut 1)
      (k : AM H (FiniteFatTree.appendRow H y g).terminalCut 1),
      (∀ j : C, H.composeAcross (trace j) g ∈ O) ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y g) U k ∧
      ∀ (j : C) (e : RawSuccessorFan H (trace j).1)
        (theta : AMExact H c (FiniteFatTree.appendRow H y g).terminalCut),
        (∀ (x : InitialNode T c), LevelTree.lev x.1 = c →
          theta.1.representative H x.1 =
            H.canonicalExtension (g.representative H) y.terminalCut (e.toFun x).1) →
        H.composeAcross theta k ∈ O :=
  review_goodPair_finite_family_of_sourceLetter H y U hyU
    (duplicateHistoryLetter H 0 y.terminalCut hpos) trace O hlarge

/-- Positive-cut compatibility wrapper for the all-exact-traces instance. -/
theorem review_goodPair_at_prefix_positive
    (n : Nat) (y : FiniteFatTree H) (hn : n ≤ y.height)
    (O : Set (AM H (FiniteFatTree.traceSourceCut H y n hn) 1))
    (U : FatTree H) (hyU : ExtendsStem H y U) (hpos : 0 < y.terminalCut)
    (hlarge : OneBlockLarge H y U
      (FixedTraceGoodRows H (FiniteFatTree.traceSourceCut H y n hn) n y hn rfl O)) :
    ∃ h k,
      FixedTraceGoodPair H (FiniteFatTree.traceSourceCut H y n hn) n y hn rfl O h k ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y h) U k :=
  review_goodPair_at_prefix_of_sourceLetter H n y hn O U hyU
    (duplicateHistoryLetter H 0 y.terminalCut hpos) hlarge

/-- Source-facing version of the local review lemma from an explicit source
letter. This includes the moving-root case. -/
theorem review_goodPair_of_sourceLetter
    (c n : Nat) (y : FiniteFatTree H) (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c)
    (O : Set (AM H c 1)) (U : FatTree H)
    (hyU : ExtendsStem H y U) (Esource : OneLevelLetter H y.terminalCut)
    (hlarge : OneBlockLarge H y U (FixedTraceGoodRows H c n y hn hsrc O)) :
    ∃ h k, FixedTraceGoodPair H c n y hn hsrc O h k ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y h) U k := by
  cases hsrc
  exact review_goodPair_at_prefix_of_sourceLetter H n y hn O U hyU Esource hlarge

/-- Source-facing positive-current-cut version of the local review lemma. -/
theorem review_goodPair_positive
    (c n : Nat) (y : FiniteFatTree H) (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c)
    (O : Set (AM H c 1)) (U : FatTree H)
    (hyU : ExtendsStem H y U) (hpos : 0 < y.terminalCut)
    (hlarge : OneBlockLarge H y U (FixedTraceGoodRows H c n y hn hsrc O)) :
    ∃ h k, FixedTraceGoodPair H c n y hn hsrc O h k ∧
      OneBlockOccurs H (FiniteFatTree.appendRow H y h) U k :=
  review_goodPair_of_sourceLetter H c n y hn hsrc O U hyU
    (duplicateHistoryLetter H 0 y.terminalCut hpos) hlarge

end SuccessorTree.SMTree.FatTree
