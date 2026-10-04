import SuccessorTree.FatTree.Reduction

/-!
# Finite fat-tree reduction witnesses

This is the finite-height half of Definition `def:subfatsubtrees`.
The cut map is defined on all `height + 1` cuts, including the terminal cut.
Thus the formal interface cannot silently omit the final-cut compatibility
needed later by the finitary order in Todorčević A.2.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- A witness that a finite fat tree `V` is a fat subtree of `U`.

The strictly increasing cut map is defined on every cut of `V`, including
its terminal cut.  The block condition is required only for actual rows. -/
structure ReductionWitness (V U : FiniteFatTree H) where
  index : Fin (V.height + 1) → Fin (U.height + 1)
  index_strict : StrictMono index
  cut_eq : ∀ i : Fin (V.height + 1), V.cut i = U.cut (index i)
  lift_subset : ∀ i : Fin V.height,
    V.oneLift H i
        (TreeLevel (T := T) (V.cut i.castSucc)) ⊆
      U.liftTo H (index i.castSucc) (index i.succ)
        (le_of_lt (index_strict
          (by
            change i.1 < i.1 + 1
            omega)))
        (TreeLevel (T := T) (U.cut (index i.castSucc)))

/-- Finite fat-subtree reduction. -/
def Reduces (V U : FiniteFatTree H) : Prop :=
  Nonempty (ReductionWitness H V U)

namespace ReductionWitness

/-- Identity is a finite reduction witness. -/
def refl (U : FiniteFatTree H) : ReductionWitness H U U where
  index := fun i => i
  index_strict := by
    intro i j hij
    exact hij
  cut_eq := by
    intro i
    rfl
  lift_subset := by
    intro i
    rw [U.liftTo_succ H i
      (TreeLevel (T := T) (U.cut i.castSucc))]

/-- Restrict a finite reduction witness to an initial segment.
The target initial segment ends at the image of the retained terminal cut. -/
def initialSegment
    {V U : FiniteFatTree H}
    (w : ReductionWitness H V U)
    (n : Nat) (hn : n ≤ V.height) :
    ReductionWitness H
      (V.initialSegment H n hn)
      (U.initialSegment H
        (w.index (⟨n, Nat.lt_succ_of_le hn⟩ :
          Fin (V.height + 1))).1
        (Nat.le_of_lt_succ
          (w.index (⟨n, Nat.lt_succ_of_le hn⟩ :
            Fin (V.height + 1))).2)) := by
  let vn : Fin (V.height + 1) :=
    ⟨n, Nat.lt_succ_of_le hn⟩
  let m : Nat := (w.index vn).1
  have hm : m ≤ U.height :=
    Nat.le_of_lt_succ (w.index vn).2
  let src : Fin (n + 1) → Fin (V.height + 1) :=
    fun i =>
      ⟨i.1, Nat.lt_succ_of_le
        ((Nat.le_of_lt_succ i.2).trans hn)⟩
  let idx : Fin (n + 1) → Fin (m + 1) :=
    fun i =>
      ⟨(w.index (src i)).1,
        Nat.lt_succ_of_le
          (w.index_strict.monotone (by
            change i.1 ≤ n
            exact Nat.le_of_lt_succ i.2))⟩
  change
    ReductionWitness H
      (V.initialSegment H n hn)
      (U.initialSegment H m hm)
  refine {
    index := idx
    index_strict := ?_
    cut_eq := ?_
    lift_subset := ?_
  }
  · intro i j hij
    change (w.index (src i)).1 < (w.index (src j)).1
    exact w.index_strict (by
      change i.1 < j.1
      exact hij)
  · intro i
    change Fin (n + 1) at i
    rw [V.initialSegment_cut H n hn i]
    rw [U.initialSegment_cut H m hm (idx i)]
    exact w.cut_eq (src i)
  · intro i
    change Fin n at i
    let iv : Fin V.height :=
      ⟨i.1, lt_of_lt_of_le i.2 hn⟩
    have h := w.lift_subset iv
    rw [V.initialSegment_oneLift H n hn i]
    rw [V.initialSegment_cut H n hn i.castSucc]
    rw [U.initialSegment_liftTo H m hm]
    rw [U.initialSegment_cut H m hm (idx i.castSucc)]
    simpa [src, idx, iv, vn, m] using h

/-- Iterate the one-block inclusions of a finite reduction witness.

The terminal cut is available in the type through the bound
`i + steps ≤ V.height`.  Source locality restricts each full-level block
inclusion to the subset actually reached by the preceding blocks. -/
theorem liftSteps_subset_liftTo
    {V U : FiniteFatTree H}
    (w : ReductionWitness H V U)
    (i steps : Nat) (hbound : i + steps ≤ V.height)
    {X Y : Set T}
    (hX : X ⊆
      TreeLevel (T := T)
        (V.cut (⟨i, by omega⟩ : Fin (V.height + 1))))
    (hY : Y ⊆
      TreeLevel (T := T)
        (U.cut (w.index
          (⟨i, by omega⟩ : Fin (V.height + 1)))))
    (hXY : X ⊆ Y) :
    V.liftSteps H i steps hbound X ⊆
      U.liftTo H
        (w.index (⟨i, by omega⟩ : Fin (V.height + 1)))
        (w.index (⟨i + steps, by omega⟩ : Fin (V.height + 1)))
        (w.index_strict.monotone (by
          change i ≤ i + steps
          omega))
        Y := by
  induction steps generalizing i X Y with
  | zero =>
      have hsame :
          (w.index (⟨i, by omega⟩ : Fin (V.height + 1))) =
            w.index (⟨i + 0, by omega⟩ : Fin (V.height + 1)) := by
        congr
      simpa [FiniteFatTree.liftTo_same, hsame] using hXY
  | succ steps ih =>
      let vi : Fin V.height := ⟨i, by omega⟩
      let v0 : Fin (V.height + 1) := vi.castSucc
      let v1 : Fin (V.height + 1) := vi.succ
      let u0 : Fin (U.height + 1) := w.index v0
      let u1 : Fin (U.height + 1) := w.index v1
      have hv01 : v0 < v1 := by
        change i < i + 1
        omega
      have hu01 : u0 ≤ u1 :=
        le_of_lt (w.index_strict hv01)
      let Y1 : Set T := U.liftTo H u0 u1 hu01 Y
      have hXvi :
          X ⊆ TreeLevel (T := T) (V.cut vi.castSucc) := by
        simpa [vi, v0] using hX
      have hY0 :
          Y ⊆ TreeLevel (T := T) (U.cut u0) := by
        simpa [vi, v0, u0] using hY
      have hX1 :
          V.oneLift H vi X ⊆
            TreeLevel (T := T) (V.cut vi.succ) :=
        V.oneLift_subset_nextLevel H vi hXvi
      have hY1 :
          Y1 ⊆ TreeLevel (T := T) (U.cut u1) := by
        dsimp [Y1]
        exact U.liftTo_subset_level H u0 u1 hu01 hY0
      have hX1Y1 : V.oneLift H vi X ⊆ Y1 := by
        intro z hz
        have hzVfull :
            z ∈ V.oneLift H vi
              (TreeLevel (T := T) (V.cut vi.castSucc)) :=
          V.oneLift_mono H vi hXvi hz
        have hzUfull : z ∈ U.liftTo H u0 u1 hu01
            (TreeLevel (T := T) (U.cut u0)) := by
          simpa [vi, v0, v1, u0, u1] using w.lift_subset vi hzVfull
        rcases V.oneLift_descends H vi hXvi hz with
          ⟨x, hx, hxz⟩
        have hsourceY : ∃ y ∈ Y, y ≤ z :=
          ⟨x, hXY hx, hxz⟩
        exact U.liftTo_mem_of_mem_of_source H
          u0 u1 hu01 hY0 (fun _ h => h) hzUfull hsourceY
      intro z hz
      rw [V.liftSteps_succ H i steps hbound X] at hz
      have hzTail :=
        ih (i := i + 1) (by omega)
          (X := V.oneLift H vi X) (Y := Y1)
          (by simpa [vi] using hX1)
          (by
            simpa [vi, v1, u1] using hY1)
          hX1Y1 hz
      let vlast : Fin (V.height + 1) :=
        ⟨i + (steps + 1), by omega⟩
      have hv1last : v1 ≤ vlast := by
        change i + 1 ≤ i + (steps + 1)
        omega
      have hu1last : u1 ≤ w.index vlast :=
        w.index_strict.monotone hv1last
      have hu0last : u0 ≤ w.index vlast :=
        hu01.trans hu1last
      have hvrec :
          (⟨i + 1 + steps, by omega⟩ :
            Fin (V.height + 1)) = vlast := by
        apply Fin.ext
        change i + 1 + steps = i + (steps + 1)
        omega
      have hvstart :
          (⟨i + 1, by omega⟩ :
            Fin (V.height + 1)) = v1 := by
        apply Fin.ext
        rfl
      let vr0 : Fin (V.height + 1) := ⟨i + 1, by omega⟩
      let vrlast : Fin (V.height + 1) :=
        ⟨i + 1 + steps, by omega⟩
      have hvr : vr0 ≤ vrlast := by
        change i + 1 ≤ i + 1 + steps
        omega
      have hur : w.index vr0 ≤ w.index vrlast :=
        w.index_strict.monotone hvr
      change
        z ∈ U.liftTo H (w.index vr0) (w.index vrlast) hur Y1 at hzTail
      have hTailSet :
          U.liftTo H (w.index vr0) (w.index vrlast) hur Y1 =
            U.liftTo H u1 (w.index vlast) hu1last Y1 :=
        U.liftTo_congr H hur hu1last
          (congrArg w.index (by simpa [vr0] using hvstart))
          (congrArg w.index (by simpa [vrlast] using hvrec))
          Y1
      have hzTail' :
          z ∈ U.liftTo H u1 (w.index vlast) hu1last Y1 := by
        rw [← hTailSet]
        exact hzTail
      have hsplit :
          z ∈ U.liftTo H u0 (w.index vlast) hu0last Y := by
        rw [U.liftTo_split H u0 u1 (w.index vlast)
          hu01 hu1last Y]
        exact hzTail'
      have hvbase :
          (⟨i, by omega⟩ :
            Fin (V.height + 1)) = v0 := by
        apply Fin.ext
        rfl
      let vend : Fin (V.height + 1) :=
        ⟨i + (steps + 1), by omega⟩
      have hvend : vlast = vend := by
        apply Fin.ext
        rfl
      have hgoalCuts :
          w.index (⟨i, by omega⟩ : Fin (V.height + 1)) ≤
            w.index vend :=
        w.index_strict.monotone (by
          change i ≤ i + (steps + 1)
          omega)
      have hOuterSet :
          U.liftTo H u0 (w.index vlast) hu0last Y =
            U.liftTo H
              (w.index (⟨i, by omega⟩ : Fin (V.height + 1)))
              (w.index vend) hgoalCuts Y :=
        U.liftTo_congr H hu0last hgoalCuts
          (congrArg w.index hvbase.symm)
          (congrArg w.index hvend) Y
      have houter :
          z ∈ U.liftTo H
            (w.index (⟨i, by omega⟩ : Fin (V.height + 1)))
            (w.index vend) hgoalCuts Y := by
        rw [← hOuterSet]
        exact hsplit
      simpa [vend] using houter

/-- A finite reduction witness carries the whole lift between any two selected
cuts into the corresponding lift of the ambient finite fat tree. -/
theorem liftTo_subset_liftTo
    {V U : FiniteFatTree H}
    (w : ReductionWitness H V U)
    (a b : Fin (V.height + 1)) (hab : a ≤ b) :
    V.liftTo H a b hab
        (TreeLevel (T := T) (V.cut a)) ⊆
      U.liftTo H (w.index a) (w.index b)
        (w.index_strict.monotone hab)
        (TreeLevel (T := T) (U.cut (w.index a))) := by
  have hlevels :
      TreeLevel (T := T) (V.cut a) ⊆
        TreeLevel (T := T) (U.cut (w.index a)) := by
    intro x hx
    change LevelTree.lev x = U.cut (w.index a)
    change LevelTree.lev x = V.cut a at hx
    rw [← w.cut_eq a]
    exact hx
  have h :=
    w.liftSteps_subset_liftTo H a.1 (b.1 - a.1)
      (by omega)
      (X := TreeLevel (T := T) (V.cut a))
      (Y := TreeLevel (T := T) (U.cut (w.index a)))
      (by
        intro x hx
        simpa using hx)
      (by
        intro x hx
        simpa using hx)
      hlevels
  intro z hz
  change z ∈ V.liftSteps H a.1 (b.1 - a.1) (by omega)
    (TreeLevel (T := T) (V.cut a)) at hz
  have hz' := h hz
  have hstart :
      (⟨a.1, by omega⟩ : Fin (V.height + 1)) = a := by
    apply Fin.ext
    rfl
  have habNat : a.1 ≤ b.1 := hab
  have hnat : a.1 + (b.1 - a.1) = b.1 :=
    Nat.add_sub_of_le habNat
  have hend :
      (⟨a.1 + (b.1 - a.1), by omega⟩ :
        Fin (V.height + 1)) = b := by
    apply Fin.ext
    exact hnat
  let a0 : Fin (V.height + 1) := ⟨a.1, by omega⟩
  let b0 : Fin (V.height + 1) :=
    ⟨a.1 + (b.1 - a.1), by omega⟩
  have hab0 : a0 ≤ b0 := by
    change a.1 ≤ a.1 + (b.1 - a.1)
    omega
  have huw0 : w.index a0 ≤ w.index b0 :=
    w.index_strict.monotone hab0
  change
    z ∈ U.liftTo H (w.index a0) (w.index b0) huw0
      (TreeLevel (T := T) (U.cut (w.index a))) at hz'
  have hEndSet :
      U.liftTo H (w.index a0) (w.index b0) huw0
          (TreeLevel (T := T) (U.cut (w.index a))) =
        U.liftTo H (w.index a) (w.index b)
          (w.index_strict.monotone hab)
          (TreeLevel (T := T) (U.cut (w.index a))) :=
    U.liftTo_congr H huw0 (w.index_strict.monotone hab)
      (congrArg w.index (by simpa [a0] using hstart))
      (congrArg w.index (by simpa [b0] using hend))
      (TreeLevel (T := T) (U.cut (w.index a)))
  rw [hEndSet] at hz'
  exact hz'

/-- Composition of finite fat-subtree reduction witnesses. -/
def trans
    {V U W : FiniteFatTree H}
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
        (wVU.index i.castSucc) (wVU.index i.succ)
        (le_of_lt (wVU.index_strict
          (by
            change i.1 < i.1 + 1
            omega))))

end ReductionWitness

/-- The finite fat-subtree relation is reflexive. -/
theorem reduces_refl (U : FiniteFatTree H) : Reduces H U U :=
  ⟨ReductionWitness.refl H U⟩

/-- The finite fat-subtree relation is transitive.  Since the witness map is
defined on `height + 1` cuts, the composed witness automatically preserves
the terminal cut. -/
theorem reduces_trans {V U W : FiniteFatTree H}
    (hVU : Reduces H V U) (hUW : Reduces H U W) :
    Reduces H V W := by
  rcases hVU with ⟨wVU⟩
  rcases hUW with ⟨wUW⟩
  exact ⟨ReductionWitness.trans H wVU wUW⟩

end FiniteFatTree

namespace FatTree.ReductionWitness

variable (H : SMTree S)

/-- Restrict an infinite reduction witness to the first `n` rows.
The target finite initial segment ends at the image of the source terminal
cut. -/
def initialSegment
    {V U : FatTree H}
    (w : FatTree.ReductionWitness H V U) (n : Nat) :
    FiniteFatTree.ReductionWitness H
      (V.initialSegment H n)
      (U.initialSegment H (w.index n)) where
  index := fun i =>
    ⟨w.index i.1,
      Nat.lt_succ_of_le
        (w.index_strict.monotone
          (Nat.le_of_lt_succ i.2))⟩
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
    change Fin n at i
    have h := w.lift_subset i.1
    rw [V.initialSegment_oneLift H n i]
    rw [U.initialSegment_liftTo H (w.index n)]
    simpa using h

end FatTree.ReductionWitness
end SMTree
end SuccessorTree
