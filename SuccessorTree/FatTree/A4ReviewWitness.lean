import SuccessorTree.FatTree.A4ReviewSplice

/-!
# The actual large-set witness under a simultaneous fan line

Exact-depth persistence is used after installing the line's head. Last-block
factorisation then recovers a member of the ORIGINAL finite bridge family.
The common tail is reattached using its full-level geometric certificate.
These arguments are independent of the colouring and the trace-good sets.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v w z
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- Composition respects transported source and intermediate cuts. -/
theorem review_composeAcross_heq
    {c d c' d' : Nat} {p : AMExact H c d} {p' : AMExact H c' d'}
    {h : AM H d 1} {h' : AM H d' 1}
    (hc : c = c') (hd : d = d') (hp : HEq p.1 p'.1) (hh : HEq h h') :
    HEq (H.composeAcross p h) (H.composeAcross p' h') := by
  cases hc
  cases hd
  have hpp : p = p' := Subtype.ext (eq_of_heq hp)
  cases hpp
  have hhh : h = h' := eq_of_heq hh
  cases hhh
  rfl

/-- Read an exact trace through an ambient prefix as a map from the fixed
literal stem's terminal cut. This does not change its representative. -/
noncomputable def reviewBridgeMap
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (a : Nat) (hya : y.height ≤ a)
    (p : FiniteFatTree.ExactTrace H (U.initialSegment H a) y.height hya) :
    AMExact H y.terminalCut (U.cut a) :=
  ⟨FiniteFatTree.castTraceRow H (terminalCut_eq_of_extendsStem H hyU) p.1, by
    simpa only [FiniteFatTree.castTraceRow_rowEndLevel] using p.rowEndLevel H⟩

theorem reviewBridgeMap_heq
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (a : Nat) (hya : y.height ≤ a)
    (p : FiniteFatTree.ExactTrace H (U.initialSegment H a) y.height hya) :
    HEq (reviewBridgeMap H y U hyU a hya p).1 p.1 :=
  FiniteFatTree.castTraceRow_heq H (terminalCut_eq_of_extendsStem H hyU) p.1

/-- Persistence guarantees a nonempty finite bridge family. A witness is
truncated at the persistent cut, not at a presumed first head. -/
theorem review_bridges_nonempty
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (hpos : 0 < y.terminalCut) (G : Set (AM H y.terminalCut 1))
    (a : Nat) (hya : y.height ≤ a)
    (hP : OneBlockExactPersistent H y U G a) :
    Nonempty (FiniteFatTree.ExactTrace H (U.initialSegment H a) y.height hya) := by
  obtain ⟨g, _, hg⟩ := hP U
    ⟨reduces_refl H U, initialSegment_extendsStem H U a⟩
  obtain ⟨p, _⟩ := exists_lastBlock_exactTrace H y U hyU hpos a hya g hg
  exact ⟨p⟩

/-- Install the line head, choose the persistent accepted row, factor it
through an original bridge, and retain the common geometric tail. -/
theorem review_persistent_line_witness
    {c : Nat} {C : Type w} {κ : Type z}
    (y : FiniteFatTree H) (U : FatTree H) (hyU : ExtendsStem H y U)
    (hpos : 0 < y.terminalCut) (G : Set (AM H y.terminalCut 1))
    (a : Nat) (hya : y.height ≤ a)
    (hP : OneBlockExactPersistent H y U G a)
    (trace : C → AM H c 1)
    (hend : ∀ j : C, (trace j).rowEndLevel H = U.cut a)
    (chi : AM H c 1 → κ) (L : ReviewFanLine H U a trace hend chi) :
    ∃ (p : FiniteFatTree.ExactTrace H (U.initialSegment H a) y.height hya)
      (g : AM H y.terminalCut 1)
      (k : AM H (FiniteFatTree.appendRow H y g).terminalCut 1),
      g ∈ G ∧ g = H.composeAcross (reviewBridgeMap H y U hyU a hya p) L.head ∧
      HEq k L.tail ∧ OneBlockOccurs H (FiniteFatTree.appendRow H y g) U k := by
  obtain ⟨V, hVcone, hVstem⟩ :=
    review_realize_head H U a L.headDepth L.head L.head_geometric
  have hyV : ExtendsStem H y V := extendsStem_of_depthCone H hyU hVcone hya
  obtain ⟨g, hgG, hgV⟩ := hP V hVcone
  obtain ⟨pV, hfactorV⟩ := exists_lastBlock_exactTrace H y V hyV hpos a hya g hgV
  have hprefix : V.initialSegment H a = U.initialSegment H a :=
    initialSegment_eq_of_extendsStem H hVcone.2
  obtain ⟨p, hpeq⟩ := review_trace_prefix_transport H U V a y.height hya hprefix pV
  have hrow : HEq (V.row a) L.head :=
    (hVstem.2 (Fin.last a)).trans
      (FiniteFatTree.appendRow_row_last H (U.initialSegment H a) L.head)
  have hcut : V.cut a = U.cut a := terminalCut_eq_of_extendsStem H hVcone.2
  have hsrc : FiniteFatTree.traceSourceCut H (V.initialSegment H a) y.height hya =
      y.terminalCut := terminalCut_eq_of_extendsStem H hyV
  have hcomp : HEq
      (H.composeAcross (exactTraceToAMExact H (V.initialSegment H a) y.height hya pV)
        (V.row a))
      (H.composeAcross (reviewBridgeMap H y U hyU a hya p) L.head) :=
    review_composeAcross_heq H hsrc hcut
      (hpeq.trans (reviewBridgeMap_heq H y U hyU a hya p).symm) hrow
  have hfactor : g = H.composeAcross (reviewBridgeMap H y U hyU a hya p) L.head :=
    eq_of_heq (hfactorV.trans hcomp)
  have hterminal : (FiniteFatTree.appendRow H y g).terminalCut = U.cut L.headDepth := by
    rw [FiniteFatTree.appendRow_terminalCut, hfactor, review_composeAcross_end]
    exact L.head_end
  obtain ⟨b, hgb⟩ := exists_stemAt_of_reduces H hgV hVcone.1
  have hb : b = L.headDepth := U.cut_injective H
    ((terminalCut_eq_of_stemAt H hgb).symm.trans hterminal)
  subst b
  let k := FiniteFatTree.castTraceRow H hterminal.symm L.tail
  have hk : OneBlockOccurs H (FiniteFatTree.appendRow H y g) U k :=
    review_occurs_after_matching_stem H (FiniteFatTree.appendRow H y g)
      U L.headDepth hgb L.tail ⟨L.tailDepth, L.tail_geometric⟩
  exact ⟨p, g, k, hgG, hfactor,
    FiniteFatTree.castTraceRow_heq H hterminal.symm L.tail, hk⟩

end SuccessorTree.SMTree.FatTree
