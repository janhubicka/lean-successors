import SuccessorTree.FatTree.A4Factor

/-!
# Fixed-source trace-good rows for fat-tree A4

This is the invariant used by the all-trace repair of A4.  A finite prefix
keeps the original source cut fixed.  A row is good when composing it after
every exact trace through the prefix lands in the chosen colour class.

This replaces the false first-block factorization used by the old fat-line
argument.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- Rows after y which have the chosen colour after every exact trace from
the fixed source cut c. -/
def FixedTraceGoodRows
    (c n : Nat)
    (y : FiniteFatTree H)
    (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c)
    (O : Set (AM H c 1)) :
    Set (AM H y.terminalCut 1) :=
  {h | ∀ q : FiniteFatTree.ExactTrace H y n hn,
      FiniteFatTree.castTraceRow H hsrc
        (H.composeAcross
          (exactTraceToAMExact H y n hn q) h) ∈ O}

/-- Appending a row preserves the fixed trace source cut. -/
theorem traceSource_eq_after_append
    (c n : Nat)
    (y : FiniteFatTree H)
    (hn : n ≤ y.height)
    (hsrc : FiniteFatTree.traceSourceCut H y n hn = c)
    (h : AM H y.terminalCut 1) :
    FiniteFatTree.traceSourceCut H
        (FiniteFatTree.appendRow H y h) n (by
          rw [FiniteFatTree.appendRow_height]
          omega) = c := by
  exact
    (FiniteFatTree.traceSourceCut_appendRow H y h n hn).trans hsrc

/-- At the terminal index, the selected trace source is the terminal cut. -/
theorem baseTraceSource
    (y : FiniteFatTree H) :
    FiniteFatTree.traceSourceCut H y y.height le_rfl =
      y.terminalCut :=
  FiniteFatTree.traceSourceCut_height H y

/-- Every exact trace through a zero-length trace interval is the identity
one-moving approximation on that cut. -/
theorem baseExactTrace_eq_id1
    (y : FiniteFatTree H)
    (q : FiniteFatTree.ExactTrace H y y.height le_rfl) :
    q.1 =
      AM.id1 H
        (FiniteFatTree.traceSourceCut H y y.height le_rfl) := by
  apply AM.eq_id1_of_topLevel_le H q.1
  change q.1.rowEndLevel H ≤
    FiniteFatTree.traceSourceCut H y y.height le_rfl
  rw [q.rowEndLevel H]
  unfold FiniteFatTree.traceTargetCut
  rw [FiniteFatTree.traceSourceCut_height H y]


/-- At the base prefix, composing after any exact trace is just the row
itself (after the harmless source-cut transport). -/
theorem cast_compose_base_exactTrace
    (y : FiniteFatTree H)
    (q : FiniteFatTree.ExactTrace H y y.height le_rfl)
    (h : AM H y.terminalCut 1) :
    FiniteFatTree.castTraceRow H (baseTraceSource H y)
        (H.composeAcross
          (exactTraceToAMExact H y y.height le_rfl q) h) = h := by
  have hq := baseExactTrace_eq_id1 H y q
  have hsource := baseTraceSource H y
  cases hsource
  have hqid :
      (exactTraceToAMExact H y y.height le_rfl q) =
        (⟨AM.id1 H y.terminalCut, AM.id1_topLevel H y.terminalCut⟩ :
          AMExact H y.terminalCut y.terminalCut) := by
    apply Subtype.ext
    exact hq
  rw [hqid]
  exact H.composeAcross_id1 y.terminalCut h

/-- Thus the fixed-source good-row set starts exactly at the chosen colour
class. -/
theorem fixedTraceGoodRows_base
    (y : FiniteFatTree H)
    (O : Set (AM H y.terminalCut 1)) :
    FixedTraceGoodRows H y.terminalCut y.height y le_rfl
      (baseTraceSource H y) O = O := by
  ext h
  constructor
  · intro hh
    have q0 : FiniteFatTree.ExactTrace H y y.height le_rfl := by
      let id : AM H
          (FiniteFatTree.traceSourceCut H y y.height le_rfl) 1 :=
        AM.id1 H
          (FiniteFatTree.traceSourceCut H y y.height le_rfl)
      refine ⟨id, ?_⟩
      constructor
      · rw [AM.id1_topLevel]
        exact baseTraceSource H y
      · intro a ha
        unfold FiniteFatTree.traceLift
        simp only [FiniteFatTree.traceSourceIndex]
        rw [FiniteFatTree.liftTo_same]
        have hid :
            id.representative H a = a := by
          exact MMap.toAM_one_representative_agrees
            H (MMap.id H)
            (FiniteFatTree.traceSourceCut H y y.height le_rfl)
            (MMap.id_fixesBelow H
              (FiniteFatTree.traceSourceCut H y y.height le_rfl))
            a (by omega)
        rw [hid]
        exact ha
    have hgood := hh q0
    rw [cast_compose_base_exactTrace H y q0 h] at hgood
    exact hgood
  · intro hh q
    rw [cast_compose_base_exactTrace H y q h]
    exact hh

end FatTree
end SMTree
end SuccessorTree
