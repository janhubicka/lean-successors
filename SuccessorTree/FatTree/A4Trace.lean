import SuccessorTree.FatTree.A4
import SuccessorTree.FatTree.Finitization

/-!
# Exact finite traces for fat-tree A4

This file formalizes the finite trace family used in the manuscript's
all-trace proof of A4. A trace starts at a selected source cut of a finite
fat tree, ends exactly at its terminal cut, and its top-level image is
contained in the corresponding finite Lift.

The first result is finiteness of the trace family. The exact update/fusion
lemmas are developed on top of this representation.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- The cut index of row n in a finite fat tree. -/
def traceSourceIndex (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) : Fin (y.height + 1) :=
  ⟨n, Nat.lt_succ_of_le hn⟩

/-- The selected source cut for traces through y beginning after n rows. -/
def traceSourceCut (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) : Nat :=
  y.cut (traceSourceIndex H y n hn)

/-- The terminal selected cut of a finite fat tree. -/
def traceTargetCut (y : FiniteFatTree H) : Nat :=
  y.terminalCut

/-- Appending one row preserves every previously selected trace source
cut. -/
theorem traceSourceCut_appendRow
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height) :
    traceSourceCut H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) =
      traceSourceCut H y n hn := by
  let i : Fin (y.height + 1) := traceSourceIndex H y n hn
  have hi :
      traceSourceIndex H (appendRow H y h) n (by
        rw [appendRow_height]
        omega) = i.castSucc := by
    apply Fin.ext
    rfl
  unfold traceSourceCut
  rw [hi]
  exact appendRow_cut_old H y h i

/-- Appending one row changes the trace target to the new terminal cut. -/
@[simp] theorem traceTargetCut_appendRow
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1) :
    traceTargetCut H (appendRow H y h) =
      h.rowEndLevel H + 1 := by
  unfold traceTargetCut
  exact appendRow_terminalCut H y h

/-- The finite Lift from the selected source cut to the terminal cut. -/
noncomputable def traceLift (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) : Set T :=
  y.liftTo H
    (traceSourceIndex H y n hn)
    (Fin.last y.height)
    (by
      change n ≤ y.height
      exact hn)
    (TreeLevel (T := T) (traceSourceCut H y n hn))

/-- The trace Lift is the iterated Lift through exactly the rows
between the selected source index and the terminal cut. -/
theorem traceLift_eq_liftSteps
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    traceLift H y n hn =
      y.liftSteps H n (y.height - n) (by omega)
        (TreeLevel (T := T) (traceSourceCut H y n hn)) := by
  rfl

/-- The old part of a trace Lift is unchanged after appending one row. -/
theorem traceLift_prefix_appendRow
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height) :
    (appendRow H y h).liftSteps H n (y.height - n) (by
      rw [appendRow_height]
      omega)
      (TreeLevel (T := T)
        (traceSourceCut H (appendRow H y h) n (by
          rw [appendRow_height]
          omega))) =
      traceLift H y n hn := by
  let z := appendRow H y h
  have hm : y.height ≤ z.height := by omega
  have hsrc :
      traceSourceCut H z n (by omega) =
        traceSourceCut H y n hn := by
    dsimp [z]
    exact traceSourceCut_appendRow H y h n hn
  have hseg :
      z.initialSegment H y.height hm = y := by
    dsimp [z]
    exact appendRow_initialSegment H y h
  have hlift :=
    z.initialSegment_liftSteps H y.height hm
      n (y.height - n) (by omega)
      (TreeLevel (T := T)
        (traceSourceCut H z n (by omega)))
  rw [hseg] at hlift
  rw [hsrc] at hlift
  rw [traceLift_eq_liftSteps H y n hn]
  exact hlift.symm

/-- Exact geometric recursion for finite-prefix traces: appending one row
applies precisely the new row Lift to the old trace Lift. -/
theorem traceLift_appendRow
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height) :
    traceLift H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) =
      (appendRow H y h).oneLift H (Fin.last y.height)
        (traceLift H y n hn) := by
  let z := appendRow H y h
  have htotal :
      z.height - n = (y.height - n) + 1 := by omega
  rw [traceLift_eq_liftSteps H z n]
  have hcongr :=
    z.liftSteps_congr_steps H n
      (z.height - n) ((y.height - n) + 1)
      (by omega) (by omega)
      htotal
      (TreeLevel (T := T)
        (traceSourceCut H z n (by omega)))
  rw [hcongr]
  rw [z.liftSteps_add H n (y.height - n) 1]
  have hidx : n + (y.height - n) = y.height := by omega
  rw [hidx]
  have hpref :
      z.liftSteps H n (y.height - n) (by omega)
        (TreeLevel (T := T)
          (traceSourceCut H z n (by
            dsimp [z]
            rw [appendRow_height]
            omega))) =
        traceLift H y n hn := by
    dsimp [z]
    exact traceLift_prefix_appendRow H y h n hn
  rw [hpref]
  rw [z.liftSteps_succ H y.height 0 (by omega)]
  rw [z.liftSteps_zero H (y.height + 1)]
  change
    z.oneLift H (⟨y.height, by omega⟩ : Fin z.height)
      (traceLift H y n hn) =
      z.oneLift H (Fin.last y.height)
        (traceLift H y n hn)
  congr 2

/-- In manuscript notation, the previous theorem says that the new trace
Lift is h-plus applied to the successor fan of the old trace Lift. -/
theorem traceLift_appendRow_fan
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height) :
    traceLift H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) =
      H.canonicalExtension (h.representative H) y.terminalCut ''
        ImmediateSuccessors (T := T) (traceLift H y n hn) := by
  rw [traceLift_appendRow H y h n hn]
  exact appendRow_oneLift_last H y h (traceLift H y n hn)

/-- Exact trace predicate used by the all-trace A4 proof.

The representative is read only on the source level, where it agrees with the
finite approximation. -/
def IsExactTrace (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height)
    (q : AM H (traceSourceCut H y n hn) 1) : Prop :=
  q.rowEndLevel H = traceTargetCut H y ∧
    ∀ a : T,
      LevelTree.lev a = traceSourceCut H y n hn →
      q.representative H a ∈ traceLift H y n hn

/-- Exact traces as a subtype. -/
def ExactTrace (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :=
  {q : AM H (traceSourceCut H y n hn) 1 //
    IsExactTrace H y n hn q}

namespace ExactTrace

/-- Forget the trace certificate. -/
def row {y : FiniteFatTree H}
    {n : Nat} {hn : n ≤ y.height}
    (q : ExactTrace H y n hn) :
    AM H (traceSourceCut H y n hn) 1 :=
  q.1

@[simp] theorem rowEndLevel
    {y : FiniteFatTree H}
    {n : Nat} {hn : n ≤ y.height}
    (q : ExactTrace H y n hn) :
    q.1.rowEndLevel H = traceTargetCut H y :=
  q.2.1

theorem image_mem_lift
    {y : FiniteFatTree H}
    {n : Nat} {hn : n ≤ y.height}
    (q : ExactTrace H y n hn)
    (a : T)
    (ha : LevelTree.lev a = traceSourceCut H y n hn) :
    q.1.representative H a ∈ traceLift H y n hn :=
  q.2.2 a ha

end ExactTrace

/-- Exact traces form a finite family. This is the finiteness input used
when the A4 proof stabilizes all trace colour profiles simultaneously. -/
theorem exactTraces_finite
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    Set.Finite
      {q : AM H (traceSourceCut H y n hn) 1 |
        IsExactTrace H y n hn q} := by
  apply
    (boundedRows_finite H
      (traceSourceCut H y n hn)
      (traceTargetCut H y + 1)).subset
  intro q hq
  have hend : q.rowEndLevel H = traceTargetCut H y := hq.1
  change q.rowEndLevel H < traceTargetCut H y + 1
  rw [hend]
  exact Nat.lt_succ_self (traceTargetCut H y)

/-- Consequently the subtype of exact traces is a finite type. -/
noncomputable instance exactTraceFinite
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    Finite (ExactTrace H y n hn) := by
  exact (exactTraces_finite H y n hn).to_subtype

end FiniteFatTree

end SMTree
end SuccessorTree
