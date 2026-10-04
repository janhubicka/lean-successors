import SuccessorTree.FatTree.Lift

/-!
# The fat-subtree reduction witness

This file begins the formalization of Definition `def:subfatsubtrees`.
Only the infinite-height relation is bundled here.  The finite relation must
also remember the terminal cut; it will be added before the Ramsey-space A.1/A.2
interface is declared.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A witness that `V` is a fat subtree of `U`, for infinite fat trees.
The local inclusion is exactly the manuscript's
`Lift_V(i,i+1) ⊆ Lift_U(φ(i),φ(i+1))`. -/
structure ReductionWitness (V U : FatTree H) where
  index : Nat → Nat
  index_strict : StrictMono index
  cut_eq : ∀ i : Nat, V.cut i = U.cut (index i)
  lift_subset : ∀ i : Nat,
    V.oneLift H i (TreeLevel (T := T) (V.cut i)) ⊆
      U.liftTo H (index i) (index (i + 1))
        (Nat.le_of_lt (index_strict (Nat.lt_succ_self i)))
        (TreeLevel (T := T) (U.cut (index i)))

/-- Infinite fat-subtree reduction. -/
def Reduces (V U : FatTree H) : Prop :=
  Nonempty (ReductionWitness H V U)

namespace ReductionWitness

/-- Alignment of the zeroth cut forces every reduction witness to start at
zero; this does not need to be a separate field in the definition. -/
theorem index_zero {V U : FatTree H}
    (w : ReductionWitness H V U) : w.index 0 = 0 := by
  apply U.cut_injective H
  calc
    U.cut (w.index 0) = V.cut 0 := (w.cut_eq 0).symm
    _ = 0 := V.cut_zero
    _ = U.cut 0 := U.cut_zero.symm

/-- Identity is a reduction witness. -/
def refl (U : FatTree H) : ReductionWitness H U U where
  index := fun i => i
  index_strict := by
    intro i j hij
    exact hij
  cut_eq := by
    intro i
    rfl
  lift_subset := by
    intro i
    rw [U.liftTo_succ H i (TreeLevel (T := T) (U.cut i))]

/-- Restrict an infinite reduction witness to the first `n` rows.
The target finite initial segment ends at the image of the source terminal
cut. -/
def initialSegment
    {V U : FatTree H}
    (w : ReductionWitness H V U) (n : Nat) :
    FiniteFatTree.ReductionWitness H
      (V.initialSegment H n)
      (U.initialSegment H (w.index n)) where
  index := fun i =>
    ⟨w.index i.1,
      by
        have hi : i.1 ≤ n := Nat.le_of_lt_succ i.2
        exact Nat.lt_succ_of_le
          (w.index_strict.monotone hi)⟩
  index_strict := by
    intro i j hij
    exact w.index_strict (by
      change i.1 < j.1
      exact hij)
  cut_eq := by
    intro i
    exact w.cut_eq i.1
  lift_subset := by
    intro i
    have h := w.lift_subset i.1
    rw [V.initialSegment_oneLift H n i]
    rw [U.initialSegment_liftTo H (w.index n)]
    simpa using h

/-- Iterate the one-block inclusions of a reduction witness while
retaining the actual subset reached at each selected cut.

The source-locality lemma for `Lift` is the key point: the manuscript
definition stores inclusions only for whole levels, but those inclusions
automatically restrict to the subset reached by the preceding blocks. -/
theorem liftSteps_subset_liftTo
    {V U : FatTree H}
    (w : ReductionWitness H V U)
    (i steps : Nat)
    {X Y : Set T}
    (hX : X ⊆ TreeLevel (T := T) (V.cut i))
    (hY : Y ⊆ TreeLevel (T := T) (U.cut (w.index i)))
    (hXY : X ⊆ Y) :
    V.liftSteps H i steps X ⊆
      U.liftTo H (w.index i) (w.index (i + steps))
        (w.index_strict.monotone (by omega)) Y := by
  induction steps generalizing i X Y with
  | zero =>
      simpa [FatTree.liftTo] using hXY
  | succ steps ih =>
      have h01 : w.index i ≤ w.index (i + 1) :=
        Nat.le_of_lt (w.index_strict (Nat.lt_succ_self i))
      let Y1 : Set T :=
        U.liftTo H (w.index i) (w.index (i + 1)) h01 Y
      have hX1 :
          V.oneLift H i X ⊆
            TreeLevel (T := T) (V.cut (i + 1)) :=
        V.oneLift_subset_nextLevel H i hX
      have hY1 :
          Y1 ⊆ TreeLevel (T := T) (U.cut (w.index (i + 1))) := by
        dsimp [Y1]
        exact U.liftTo_subset_level H
          (w.index i) (w.index (i + 1)) h01 hY
      have hX1Y1 : V.oneLift H i X ⊆ Y1 := by
        intro z hz
        have hzVfull :
            z ∈ V.oneLift H i
              (TreeLevel (T := T) (V.cut i)) :=
          V.oneLift_mono H i hX hz
        have hzUfull := w.lift_subset i hzVfull
        rcases V.oneLift_descends H i hX hz with
          ⟨x, hx, hxz⟩
        have hsourceY : ∃ y ∈ Y, y ≤ z :=
          ⟨x, hXY hx, hxz⟩
        exact U.liftTo_mem_of_mem_of_source H
          (w.index i) (w.index (i + 1)) h01
          hY (fun _ h => h) hzUfull hsourceY
      intro z hz
      change
        z ∈ V.liftSteps H (i + 1) steps
          (V.oneLift H i X) at hz
      have hzTail :=
        ih (i := i + 1)
          (X := V.oneLift H i X) (Y := Y1)
          hX1 hY1 hX1Y1 hz
      have h1last :
          w.index (i + 1) ≤ w.index (i + (steps + 1)) :=
        w.index_strict.monotone (by omega)
      rw [U.liftTo_split H
        (w.index i) (w.index (i + 1))
        (w.index (i + (steps + 1))) h01 h1last Y]
      have hend : i + 1 + steps = i + (steps + 1) := by omega
      change
        z ∈ U.liftSteps H (w.index (i + 1))
          (w.index (i + (steps + 1)) - w.index (i + 1))
          (U.liftTo H (w.index i) (w.index (i + 1)) h01 Y)
      change
        z ∈ U.liftSteps H (w.index (i + 1))
          (w.index (i + 1 + steps) - w.index (i + 1)) Y1 at hzTail
      simpa only [hend, Y1] using hzTail

/-- A reduction witness carries the whole lift between any two selected
cuts into the corresponding lift of the ambient fat tree. -/
theorem liftTo_subset_liftTo
    {V U : FatTree H}
    (w : ReductionWitness H V U)
    (i k : Nat) (hik : i ≤ k) :
    V.liftTo H i k hik
        (TreeLevel (T := T) (V.cut i)) ⊆
      U.liftTo H (w.index i) (w.index k)
        (w.index_strict.monotone hik)
        (TreeLevel (T := T) (U.cut (w.index i))) := by
  have hlevels :
      TreeLevel (T := T) (V.cut i) ⊆
        TreeLevel (T := T) (U.cut (w.index i)) := by
    intro x hx
    change LevelTree.lev x = U.cut (w.index i)
    change LevelTree.lev x = V.cut i at hx
    rw [← w.cut_eq i]
    exact hx
  have h :=
    w.liftSteps_subset_liftTo H i (k - i)
      (X := TreeLevel (T := T) (V.cut i))
      (Y := TreeLevel (T := T) (U.cut (w.index i)))
      (fun _ hx => hx) (fun _ hx => hx) hlevels
  have hidx : i + (k - i) = k := by omega
  simpa [FatTree.liftTo, hidx] using h

/-- Composition of fat-subtree reduction witnesses. -/
def trans
    {V U W : FatTree H}
    (wVU : ReductionWitness H V U)
    (wUW : ReductionWitness H U W) :
    ReductionWitness H V W where
  index := fun i => wUW.index (wVU.index i)
  index_strict := wUW.index_strict.comp wVU.index_strict
  cut_eq := by
    intro i
    calc
      V.cut i = U.cut (wVU.index i) := wVU.cut_eq i
      _ = W.cut (wUW.index (wVU.index i)) :=
        wUW.cut_eq (wVU.index i)
  lift_subset := by
    intro i
    exact (wVU.lift_subset i).trans
      (wUW.liftTo_subset_liftTo H
        (wVU.index i) (wVU.index (i + 1))
        (Nat.le_of_lt
          (wVU.index_strict (Nat.lt_succ_self i))))

end ReductionWitness

/-- The infinite fat-subtree relation is reflexive. -/
theorem reduces_refl (U : FatTree H) : Reduces H U U :=
  ⟨ReductionWitness.refl H U⟩

/-- The infinite fat-subtree relation is transitive. -/
theorem reduces_trans {V U W : FatTree H}
    (hVU : Reduces H V U) (hUW : Reduces H U W) :
    Reduces H V W := by
  rcases hVU with ⟨wVU⟩
  rcases hUW with ⟨wUW⟩
  exact ⟨ReductionWitness.trans H wVU wUW⟩

end FatTree

end SMTree
end SuccessorTree
