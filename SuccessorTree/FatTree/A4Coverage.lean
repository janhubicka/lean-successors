import SuccessorTree.FatTree.A4Good
import SuccessorTree.FatTree.A4Large

/-!
# Coverage of arbitrary geometric one-step extensions

This is the final coverage implication in the corrected A4 fusion: if every
ambient row is good after every exact trace from the original source cut,
then every geometric one-step extension has the desired colour. The argument
factors through the last ambient block, never the first selected block.

Constructing a refinement satisfying the invariant is a separate obligation;
this file does not assert the full A4 theorem.
-/

namespace SuccessorTree.SMTree.FatTree

universe u v
variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label} (H : SMTree S)

/-- The source cut of an exact trace remains the terminal cut of the original
literal stem, however far along the ambient tree that trace ends. -/
theorem initialSegment_traceSource_of_extendsStem
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U) (m : Nat) (hym : y.height ≤ m) :
    FiniteFatTree.traceSourceCut H (U.initialSegment H m) y.height hym =
      y.terminalCut := by
  change U.cut y.height = y.terminalCut
  exact terminalCut_eq_of_extendsStem H hyU

/-- An appended row necessarily occurs strictly after the stem's height. -/
theorem height_lt_of_appended_stemAt
    (y : FiniteFatTree H) (U : FatTree H)
    (g : AM H y.terminalCut 1) (k : Nat)
    (hg : StemAt H (FiniteFatTree.appendRow H y g) U k) :
    y.height < k := by
  rcases hg.1 with ⟨w⟩
  have h := w.height_le H
  change y.height + 1 ≤ k at h
  omega

/-- Last-block coverage of the all-trace invariant.  The exact hypothesis is
that every node on the original source cut has an immediate successor.  A
source letter supplies this at a moving root; the no-letter root case is
handled separately by row uniqueness. -/
theorem oneBlock_mem_of_all_fixedTraceGoodRows_of_successors
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U)
    (hsuccessors :
      ∀ x : T, LevelTree.lev x = y.terminalCut → ∃ z : T, x ⋖ z)
    (O : Set (AM H y.terminalCut 1))
    (hgood : ∀ (m : Nat) (hym : y.height ≤ m),
      U.row m ∈ FixedTraceGoodRows H y.terminalCut y.height
        (U.initialSegment H m) hym
        (initialSegment_traceSource_of_extendsStem H y U hyU m hym) O)
    (g : AM H y.terminalCut 1) (hg : OneBlockOccurs H y U g) :
    g ∈ O := by
  rcases hg with ⟨k, hgk⟩
  have hheight := height_lt_of_appended_stemAt H y U g k hgk
  cases k with
  | zero => omega
  | succ m =>
      have hym : y.height ≤ m := by omega
      obtain ⟨p, hp⟩ := exists_lastBlock_exactTrace_of_successors H
        y U hyU hsuccessors m hym g hgk
      let hsrc := initialSegment_traceSource_of_extendsStem H y U hyU m hym
      let comp := H.composeAcross
        (exactTraceToAMExact H (U.initialSegment H m) y.height hym p)
        (U.row m)
      have hcolour : FiniteFatTree.castTraceRow H hsrc comp ∈ O :=
        hgood m hym p
      have hcast := FiniteFatTree.castTraceRow_heq H hsrc comp
      have heq : g = FiniteFatTree.castTraceRow H hsrc comp :=
        eq_of_heq (hp.trans hcast.symm)
      rw [heq]
      exact hcolour

/-- A source letter supplies the successor hypothesis needed for coverage,
including at a moving root. -/
theorem oneBlock_mem_of_all_fixedTraceGoodRows_of_sourceLetter
    (y : FiniteFatTree H) (U : FatTree H)
    (hyU : ExtendsStem H y U) (E : OneLevelLetter H y.terminalCut)
    (O : Set (AM H y.terminalCut 1))
    (hgood : ∀ (m : Nat) (hym : y.height ≤ m),
      U.row m ∈ FixedTraceGoodRows H y.terminalCut y.height
        (U.initialSegment H m) hym
        (initialSegment_traceSource_of_extendsStem H y U hyU m hym) O)
    (g : AM H y.terminalCut 1) (hg : OneBlockOccurs H y U g) :
    g ∈ O :=
  oneBlock_mem_of_all_fixedTraceGoodRows_of_successors H y U hyU
    (fun x hx => ⟨E.toMMap x, H.letter_covBy E hx⟩) O hgood g hg

end SuccessorTree.SMTree.FatTree
