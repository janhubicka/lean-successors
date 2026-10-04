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
