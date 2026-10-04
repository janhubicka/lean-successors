import SuccessorTree.FatTree.A4
import SuccessorTree.FatTree.Finitization
import SuccessorTree.ShapeSplit

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

/-- Every endpoint of a finite trace Lift lies on the terminal cut of
the finite fat tree. -/
theorem traceLift_subset_targetLevel
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    traceLift H y n hn ⊆
      TreeLevel (T := T) (traceTargetCut H y) := by
  unfold traceLift traceTargetCut
  apply y.liftTo_subset_level H
  intro a ha
  exact ha

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
  have hm : y.height ≤ z.height := by
    dsimp [z]
    exact Nat.le_succ y.height
  have hzN : n ≤ z.height := hn.trans hm
  have hsrc :
      traceSourceCut H z n hzN =
        traceSourceCut H y n hn := by
    dsimp [z]
    exact traceSourceCut_appendRow H y h n hn
  have hseg :
      z.initialSegment H y.height hm = y := by
    dsimp [z]
    exact appendRow_initialSegment H y h
  let Xz : Set T :=
    TreeLevel (T := T) (traceSourceCut H z n hzN)
  have hboundSeg :
      n + (y.height - n) ≤
        (z.initialSegment H y.height hm).height := by
    change n + (y.height - n) ≤ y.height
    omega
  have hboundZ : n + (y.height - n) ≤ z.height := by
    exact (by
      have : n + (y.height - n) ≤ y.height := by omega
      exact this.trans hm)
  have hboundY : n + (y.height - n) ≤ y.height := by
    omega
  have hinside :=
    z.initialSegment_liftSteps H y.height hm
      n (y.height - n) hboundSeg Xz
  have htree :=
    FiniteFatTree.liftSteps_congr_tree H hseg
      n (y.height - n) hboundSeg hboundY Xz
  have hamb :
      z.liftSteps H n (y.height - n) hboundZ Xz =
        y.liftSteps H n (y.height - n) hboundY Xz :=
    hinside.symm.trans htree
  have hX :
      Xz =
        TreeLevel (T := T) (traceSourceCut H y n hn) := by
    unfold Xz
    rw [hsrc]
  have hamb' :
      z.liftSteps H n (y.height - n) hboundZ
          (TreeLevel (T := T) (traceSourceCut H y n hn)) =
        y.liftSteps H n (y.height - n) hboundY
          (TreeLevel (T := T) (traceSourceCut H y n hn)) := by
    simpa [hX] using hamb
  change
    z.liftSteps H n (y.height - n) _
        (TreeLevel (T := T) (traceSourceCut H z n _)) =
      traceLift H y n hn
  rw [traceLift_eq_liftSteps H y n hn]
  have hsrc' :
      TreeLevel (T := T) (traceSourceCut H z n hzN) =
        TreeLevel (T := T) (traceSourceCut H y n hn) := by
    rw [hsrc]
  simpa [hsrc'] using hamb'

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
  have hzheight : z.height = y.height + 1 := by
    rfl
  have hzN : n ≤ z.height := by
    rw [hzheight]
    omega
  let Xz : Set T :=
    TreeLevel (T := T) (traceSourceCut H z n hzN)
  have htotal :
      z.height - n = (y.height - n) + 1 := by
    rw [hzheight]
    omega
  have hwhole : n + (z.height - n) ≤ z.height := by
    omega
  have hsplit : n + ((y.height - n) + 1) ≤ z.height := by
    rw [hzheight]
    omega
  have hprefix : n + (y.height - n) ≤ z.height := by
    rw [hzheight]
    omega
  have hlast : y.height + 1 ≤ z.height := by
    rw [hzheight]
  have hcongr :=
    z.liftSteps_congr_steps H n
      (z.height - n) ((y.height - n) + 1)
      hwhole hsplit htotal Xz
  have hadd :=
    z.liftSteps_add H n (y.height - n) 1 hsplit Xz
  have hidx : n + (y.height - n) = y.height := by
    omega
  let P : Set T :=
    z.liftSteps H n (y.height - n) hprefix Xz
  have hstart :
      z.liftSteps H (n + (y.height - n)) 1 (by omega) P =
        z.liftSteps H y.height 1 hlast P := by
    exact z.liftSteps_congr_start H
      (n + (y.height - n)) y.height 1
      (by omega) hlast hidx P
  have hpref :
      P = traceLift H y n hn := by
    unfold P Xz
    have hp := traceLift_prefix_appendRow H y h n hn
    change
      z.liftSteps H n (y.height - n) _
          (TreeLevel (T := T) (traceSourceCut H z n _)) =
        traceLift H y n hn at hp
    exact hp
  have hsub :
      z.liftSteps H y.height 1 hlast P =
        z.liftSteps H y.height 1 hlast (traceLift H y n hn) :=
    congrArg (fun X => z.liftSteps H y.height 1 hlast X) hpref
  have hone :=
    z.liftSteps_one H y.height hlast (traceLift H y n hn)
  rw [traceLift_eq_liftSteps H z n]
  change
    z.liftSteps H n (z.height - n) _ Xz =
      (appendRow H y h).oneLift H (Fin.last y.height)
        (traceLift H y n hn)
  calc
    z.liftSteps H n (z.height - n) _ Xz =
        z.liftSteps H n ((y.height - n) + 1) _ Xz :=
      hcongr
    _ = z.liftSteps H (n + (y.height - n)) 1 _ P := by
      simpa [P] using hadd
    _ = z.liftSteps H y.height 1 hlast P := hstart
    _ = z.liftSteps H y.height 1 hlast (traceLift H y n hn) := hsub
    _ = z.oneLift H
          (⟨y.height, by omega⟩ : Fin z.height)
          (traceLift H y n hn) := hone
    _ = (appendRow H y h).oneLift H (Fin.last y.height)
          (traceLift H y n hn) := by
      let j : Fin (appendRow H y h).height :=
        ⟨y.height, by
          rw [appendRow_height]
          exact Nat.lt_succ_self y.height⟩
      have hidx :
          j =
            (Fin.last y.height :
              Fin (appendRow H y h).height) := by
        apply Fin.ext
        rfl
      simpa [z, j] using congrArg
        (fun j : Fin (appendRow H y h).height =>
          (appendRow H y h).oneLift H j
            (traceLift H y n hn)) hidx

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

/-- An exact trace of an appended tree has the expected new terminal
image level. -/
theorem ExactTrace.appendRow_rowEnd
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega)) :
    q.1.rowEndLevel H = h.rowEndLevel H + 1 := by
  calc
    q.1.rowEndLevel H =
        traceTargetCut H (appendRow H y h) :=
      q.rowEndLevel H
    _ = h.rowEndLevel H + 1 :=
      traceTargetCut_appendRow H y h

/-- Geometric half of the exact trace update: every image point of an exact
trace after appending `h` lies in the canonical image under `h⁺` of an
immediate successor of the old trace lift. -/
theorem ExactTrace.appendRow_image_mem_fan
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega))
    (a : T)
    (ha :
      LevelTree.lev a =
        traceSourceCut H (appendRow H y h) n (by
          rw [appendRow_height]
          omega)) :
    q.1.representative H a ∈
      H.canonicalExtension (h.representative H) y.terminalCut ''
        ImmediateSuccessors (T := T) (traceLift H y n hn) := by
  have hm := q.image_mem_lift H a ha
  rw [traceLift_appendRow_fan H y h n hn] at hm
  exact hm

/-- Consequently the subtype of exact traces is a finite type. -/
noncomputable instance exactTraceFinite
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    Finite (ExactTrace H y n hn) := by
  exact (exactTraces_finite H y n hn).to_subtype

/-- The selected source cut of a trace never lies above its terminal
cut. -/
theorem traceSourceCut_le_target
    (y : FiniteFatTree H)
    (n : Nat) (hn : n ≤ y.height) :
    traceSourceCut H y n hn ≤ traceTargetCut H y := by
  unfold traceSourceCut traceTargetCut
  exact y.cut_le_terminalCut H (traceSourceIndex H y n hn)

/-- Transport a one-row finite approximation along equality of its
source cut.  The underlying row data and its total representative do not
change; only the dependent source-cut index is transported. -/
def castTraceRow {a b : Nat} (h : a = b) (q : AM H a 1) : AM H b 1 := by
  cases h
  exact q

@[simp] theorem castTraceRow_rowEndLevel
    {a b : Nat} (h : a = b) (q : AM H a 1) :
    (castTraceRow H h q).rowEndLevel H = q.rowEndLevel H := by
  cases h
  rfl

@[simp] theorem castTraceRow_representative
    {a b : Nat} (h : a = b) (q : AM H a 1) :
    (castTraceRow H h q).representative H = q.representative H := by
  cases h
  rfl

theorem castTraceRow_heq
    {a b : Nat} (h : a = b) (q : AM H a 1) :
    HEq (castTraceRow H h q) q := by
  cases h
  rfl

/-- Raw successor-table data for an admissible candidate trace.

Unlike `ExactTrace.extendByLetter`, this does not assume that the successor
choices come from a total admissible one-level M-map.  It records exactly the
finite table used in the manuscript: pointwise immediate successors of the
old trace, followed by the canonical appended row. -/
def IsRawTraceCandidate
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H y n hn)
    (theta : AM H
      (traceSourceCut H (appendRow H y h) n (by
        rw [appendRow_height]
        omega)) 1) : Prop :=
  theta.rowEndLevel H = traceTargetCut H (appendRow H y h) ∧
    ∀ a : T, LevelTree.lev a = traceSourceCut H y n hn →
      ∃ z : T,
        q.1.representative H a ⋖ z ∧
        theta.representative H a =
          H.canonicalExtension (h.representative H) y.terminalCut z

/-- Every admissible row carrying the manuscript's raw successor-table data
satisfies the exact-trace predicate for the appended finite fat tree.  No
total admissible map extending the successor table is used. -/
theorem isExactTrace_of_raw_candidate
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H y n hn)
    (theta : AM H
      (traceSourceCut H (appendRow H y h) n (by
        rw [appendRow_height]
        omega)) 1)
    (hraw : IsRawTraceCandidate H y h n hn q theta) :
    IsExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) theta := by
  refine ⟨hraw.1, ?_⟩
  intro a ha
  have hsrc :
      traceSourceCut H (appendRow H y h) n (by
        rw [appendRow_height]
        omega) =
        traceSourceCut H y n hn :=
    traceSourceCut_appendRow H y h n hn
  have ha0 :
      LevelTree.lev a = traceSourceCut H y n hn :=
    ha.trans hsrc
  rcases hraw.2 a ha0 with ⟨z, hqz, htheta⟩
  have hqmem :
      q.1.representative H a ∈ traceLift H y n hn :=
    q.image_mem_lift H a ha0
  rw [traceLift_appendRow_fan H y h n hn]
  rw [htheta]
  exact ⟨z, ⟨q.1.representative H a, hqmem, hqz⟩, rfl⟩

/-- Package the preceding proposition as an exact-trace object. -/
noncomputable def exactTraceOfRawCandidate
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H y n hn)
    (theta : AM H
      (traceSourceCut H (appendRow H y h) n (by
        rw [appendRow_height]
        omega)) 1)
    (hraw : IsRawTraceCandidate H y h n hn q theta) :
    ExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) :=
  ⟨theta, isExactTrace_of_raw_candidate H y h n hn q theta hraw⟩

/-- Manuscript trace-update relation.

The intermediate successor table is deliberately *raw finite data*: for each
source-level point it chooses an immediate successor of the old trace value,
whose image under the canonical appended row is the new trace value.  No
admissible total M-map extending this table is required.  This matches the
manuscript's successor-table set \(\mathscr E(q)\). -/
def IsRawTraceUpdate
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H y n hn)
    (theta : ExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega)) : Prop :=
  ∀ a : T, LevelTree.lev a = traceSourceCut H y n hn →
    ∃ z : T,
      q.1.representative H a ⋖ z ∧
      theta.1.representative H a =
        H.canonicalExtension (h.representative H) y.terminalCut z

/-- Forward exact-trace update.

Given an exact trace `q` through `y`, a one-level successor letter `e`
at the old terminal cut, and the next ambient row `h`, the literal
composite `h⁺ ∘ e ∘ q` is an exact trace through `y ⌢ h`.
This is the constructive inclusion `Q_y[h] ⊆ Q_{y⌢h}` from the manuscript. -/
noncomputable def ExactTrace.extendByLetter
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (q : ExactTrace H y n hn)
    (e : OneLevelLetter H y.terminalCut) :
    ExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) := by
  let c0 : Nat := traceSourceCut H y n hn
  let d : Nat := y.terminalCut
  let C : MMap H :=
    H.canonicalExtension (h.representative H) d
  let F : MMap H :=
    MMap.comp H C
      (MMap.comp H e.toMMap (q.1.representative H))
  have hcd : c0 ≤ d := by
    dsimp [c0, d]
    exact traceSourceCut_le_target H y n hn
  have hCfix : C.FixesBelow H c0 := by
    intro x hx
    have hxd : LevelTree.lev x < d :=
      lt_of_lt_of_le hx hcd
    dsimp [C]
    rw [H.canonicalExtension_agrees
      (h.representative H) d x (Nat.le_of_lt hxd)]
    exact h.representative_fixesBelow H x hxd
  have hefix : e.toMMap.FixesBelow H c0 := by
    intro x hx
    exact e.eq_id_below H (lt_of_lt_of_le hx hcd)
  have hqfix :
      (q.1.representative H).FixesBelow H c0 := by
    exact q.1.representative_fixesBelow H
  have hinner :
      (MMap.comp H e.toMMap
        (q.1.representative H)).FixesBelow H c0 :=
    MMap.comp_fixesBelow H e.toMMap
      (q.1.representative H) c0 hefix hqfix
  have hFfix : F.FixesBelow H c0 := by
    exact MMap.comp_fixesBelow H C
      (MMap.comp H e.toMMap (q.1.representative H))
      c0 hCfix hinner
  let theta : AM H c0 1 :=
    F.toAM H c0 1 hFfix
  have hsrc :
      traceSourceCut H (appendRow H y h) n (by
        rw [appendRow_height]
        omega) = c0 := by
    dsimp [c0]
    exact traceSourceCut_appendRow H y h n hn
  have hthetaTop :
      theta.rowEndLevel H = h.rowEndLevel H + 1 := by
    change theta.topLevel H = h.rowEndLevel H + 1
    rw [show theta.topLevel H = H.levelMap F.map c0 by
      exact MMap.toAM_one_topLevel H F c0 hFfix]
    obtain ⟨a, ha⟩ := H.level_nonempty c0
    have hqa :
        LevelTree.lev (q.1.representative H a) = d := by
      calc
        LevelTree.lev (q.1.representative H a) =
            H.levelMap (q.1.representative H).map c0 := by
          simpa [ha] using
            (H.levelMap_eq (q.1.representative H).map (a := a)).symm
        _ = q.1.rowEndLevel H := rfl
        _ = traceTargetCut H y := q.rowEndLevel H
        _ = d := rfl
    have hea :
        LevelTree.lev (e.toMMap (q.1.representative H a)) =
          d + 1 := by
      exact e.level_succ_at H hqa
    calc
      H.levelMap F.map c0 =
          LevelTree.lev (F a) := by
        simpa [ha] using H.levelMap_eq F.map (a := a)
      _ =
          LevelTree.lev
            (C (e.toMMap (q.1.representative H a))) := rfl
      _ =
          H.levelMap C.map
            (LevelTree.lev
              (e.toMMap (q.1.representative H a))) := by
        exact
          (H.levelMap_eq C.map
            (a := e.toMMap (q.1.representative H a))).symm
      _ = H.levelMap C.map (d + 1) := by rw [hea]
      _ = H.levelMap C.map d + 1 := by
        exact H.canonicalExtension_level_succ
          (h.representative H) d d le_rfl
      _ =
          H.levelMap (h.representative H).map d + 1 := by
        dsimp [C]
        rw [H.canonicalExtension_level_at_prefix
          (h.representative H) d]
      _ = h.rowEndLevel H + 1 := rfl
  let c1 : Nat :=
    traceSourceCut H (appendRow H y h) n (by
      rw [appendRow_height]
      omega)
  let theta' : AM H c1 1 :=
    castTraceRow H hsrc.symm theta
  refine ⟨theta', ?_, ?_⟩
  · calc
      theta'.rowEndLevel H = theta.rowEndLevel H := by
        simp [theta']
      _ = h.rowEndLevel H + 1 := hthetaTop
      _ = traceTargetCut H (appendRow H y h) :=
        (traceTargetCut_appendRow H y h).symm
  · intro a ha
    have ha0 : LevelTree.lev a = c0 := by
      exact ha.trans hsrc
    have htheta :
        theta.representative H a = F a :=
      MMap.toAM_one_representative_agrees
        H F c0 hFfix a (by omega)
    have htheta' :
        theta'.representative H a = F a := by
      calc
        theta'.representative H a =
            theta.representative H a := by
          simp [theta']
        _ = F a := htheta
    have hqmem :
        q.1.representative H a ∈ traceLift H y n hn := by
      apply q.image_mem_lift H a
      exact ha0
    have hqlev :
        LevelTree.lev (q.1.representative H a) = d := by
      calc
        LevelTree.lev (q.1.representative H a) =
            H.levelMap (q.1.representative H).map c0 := by
          simpa [ha0] using
            (H.levelMap_eq (q.1.representative H).map (a := a)).symm
        _ = q.1.rowEndLevel H := rfl
        _ = traceTargetCut H y := q.rowEndLevel H
        _ = d := rfl
    rw [traceLift_appendRow_fan H y h n hn]
    rw [htheta']
    refine ⟨e.toMMap (q.1.representative H a), ?_, rfl⟩
    exact ⟨q.1.representative H a, hqmem,
      H.letter_covBy e hqlev⟩

/-- Reverse exact-trace update.

Every exact trace through the appended tree has a predecessor exact trace
through the old finite tree.  Pointwise, the new trace is obtained by
choosing immediate successors of the predecessor trace and then applying
the canonical extension of the appended row.  This is the missing reverse
inclusion in the manuscript identity `Q_{y⌢h}=Q_y[h]`. -/
theorem ExactTrace.exists_raw_predecessor
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (theta : ExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega)) :
    ∃ q : ExactTrace H y n hn,
      IsRawTraceUpdate H y h n hn q theta := by
  let c0 : Nat := traceSourceCut H y n hn
  let c1 : Nat :=
    traceSourceCut H (appendRow H y h) n (by
      rw [appendRow_height]
      omega)
  let d : Nat := traceTargetCut H y
  have hsrc : c1 = c0 := by
    dsimp [c0, c1]
    exact traceSourceCut_appendRow H y h n hn
  let theta0 : AM H c0 1 :=
    castTraceRow H hsrc theta.1
  have hcd : c0 ≤ d := by
    dsimp [c0, d]
    exact traceSourceCut_le_target H y n hn
  have hdhtop : d ≤ h.rowEndLevel H := by
    change y.terminalCut ≤ h.topLevel H
    exact H.levelMap_id_le (h.representative H).map y.terminalCut
  have hthetaTop : theta0.topLevel H = h.rowEndLevel H + 1 := by
    change theta0.rowEndLevel H = h.rowEndLevel H + 1
    calc
      theta0.rowEndLevel H = theta.1.rowEndLevel H := by
        simp [theta0]
      _ = h.rowEndLevel H + 1 :=
        theta.appendRow_rowEnd H y h n hn
  have hdt : d ≤ theta0.topLevel H := by
    rw [hthetaTop]
    omega
  obtain ⟨qrow, hqtop, hqle⟩ :=
    exists_truncate_oneRow H theta0 d hcd hdt
  have hqExact : IsExactTrace H y n hn qrow := by
    refine ⟨?_, ?_⟩
    · change qrow.topLevel H = traceTargetCut H y
      simpa [d] using hqtop
    · intro a ha
      have ha0 : LevelTree.lev a = c0 := by
        change LevelTree.lev a = c0 at ha
        exact ha
      have ha1 : LevelTree.lev a = c1 := by
        exact ha0.trans hsrc.symm
      have hthetaFan :=
        theta.appendRow_image_mem_fan H y h n hn a ha1
      rcases hthetaFan with
        ⟨z, ⟨t, htLift, htz⟩, hthetaZ⟩
      have htLevel :
          LevelTree.lev t = d := by
        have htTarget :=
          traceLift_subset_targetLevel H y n hn htLift
        exact htTarget
      have hqLevel :
          LevelTree.lev (qrow.representative H a) = d := by
        calc
          LevelTree.lev (qrow.representative H a) =
              H.levelMap (qrow.representative H).map c0 := by
            simpa [ha] using
              (H.levelMap_eq (qrow.representative H).map (a := a)).symm
          _ = qrow.topLevel H := rfl
          _ = d := hqtop
      have htheta0Eq :
          theta0.representative H a = theta.1.representative H a := by
        simp [theta0]
      have hqTheta :
          qrow.representative H a ≤ theta.1.representative H a := by
        have hq0 := hqle a ha0
        rwa [htheta0Eq] at hq0
      let C : MMap H :=
        H.canonicalExtension (h.representative H) y.terminalCut
      have hCfix : C.FixesBelow H d := by
        intro x hx
        have hxd : LevelTree.lev x < y.terminalCut := by
          change LevelTree.lev x < traceTargetCut H y at hx
          exact hx
        dsimp [C]
        rw [H.canonicalExtension_agrees
          (h.representative H) y.terminalCut x (Nat.le_of_lt hxd)]
        exact h.representative_fixesBelow H x hxd
      have htC : t ≤ C t :=
        C.le_apply_at_cut H d hCfix (by simpa [d] using htLevel)
      have hCmono : C t ≤ C z :=
        C.map.map_le_of_le htz.le
      have htTheta :
          t ≤ theta.1.representative H a := by
        rw [← hthetaZ]
        exact htC.trans hCmono
      have hqt : qrow.representative H a = t := by
        rcases LevelTree.comparable_below hqTheta htTheta with h | h
        · exact LevelTree.same_level_of_le h
            (hqLevel.trans htLevel.symm)
        · exact (LevelTree.same_level_of_le h
            (htLevel.trans hqLevel.symm)).symm
      rw [hqt]
      exact htLift
  let q : ExactTrace H y n hn := ⟨qrow, hqExact⟩
  refine ⟨q, ?_⟩
  intro a ha
  have ha0 : LevelTree.lev a = c0 := by
    change LevelTree.lev a = c0 at ha
    exact ha
  have ha1 : LevelTree.lev a = c1 := by
    exact ha0.trans hsrc.symm
  have hthetaFan :=
    theta.appendRow_image_mem_fan H y h n hn a ha1
  rcases hthetaFan with
    ⟨z, ⟨t, htLift, htz⟩, hthetaZ⟩
  have htLevel :
      LevelTree.lev t = d :=
    traceLift_subset_targetLevel H y n hn htLift
  have hqLevel :
      LevelTree.lev (q.1.representative H a) = d := by
    calc
      LevelTree.lev (q.1.representative H a) =
          H.levelMap (q.1.representative H).map c0 := by
        simpa [ha] using
          (H.levelMap_eq (q.1.representative H).map (a := a)).symm
      _ = q.1.topLevel H := rfl
      _ = d := hqtop
  have htheta0Eq :
      theta0.representative H a = theta.1.representative H a := by
    simp [theta0]
  have hqTheta :
      q.1.representative H a ≤ theta.1.representative H a := by
    have hq0 := hqle a ha0
    rwa [htheta0Eq] at hq0
  let C : MMap H :=
    H.canonicalExtension (h.representative H) y.terminalCut
  have hCfix : C.FixesBelow H d := by
    intro x hx
    have hxd : LevelTree.lev x < y.terminalCut := by
      change LevelTree.lev x < traceTargetCut H y at hx
      exact hx
    dsimp [C]
    rw [H.canonicalExtension_agrees
      (h.representative H) y.terminalCut x (Nat.le_of_lt hxd)]
    exact h.representative_fixesBelow H x hxd
  have htC : t ≤ C t :=
    C.le_apply_at_cut H d hCfix (by simpa [d] using htLevel)
  have hCmono : C t ≤ C z :=
    C.map.map_le_of_le htz.le
  have htTheta :
      t ≤ theta.1.representative H a := by
    rw [← hthetaZ]
    exact htC.trans hCmono
  have hqt : q.1.representative H a = t := by
    rcases LevelTree.comparable_below hqTheta htTheta with h | h
    · exact LevelTree.same_level_of_le h
        (hqLevel.trans htLevel.symm)
    · exact (LevelTree.same_level_of_le h
        (htLevel.trans hqLevel.symm)).symm
  refine ⟨z, ?_, ?_⟩
  · simpa [hqt] using htz
  · exact hthetaZ.symm


/-- Exact finite-prefix trace update, in the bidirectional manuscript form.

An admissible row is an exact trace through `y ⌢ h` iff it is obtained from
some exact trace through `y` by a raw successor-table update followed by
the canonical appended row.  This is the formal equality
`Q_{y⌢h} = Q_y[h]`. -/
theorem isExactTrace_appendRow_iff
    (y : FiniteFatTree H)
    (h : AM H y.terminalCut 1)
    (n : Nat) (hn : n ≤ y.height)
    (theta : AM H
      (traceSourceCut H (appendRow H y h) n (by
        rw [appendRow_height]
        omega)) 1) :
    IsExactTrace H (appendRow H y h) n (by
      rw [appendRow_height]
      omega) theta ↔
      ∃ q : ExactTrace H y n hn,
        IsRawTraceCandidate H y h n hn q theta := by
  constructor
  · intro htheta
    let Theta : ExactTrace H (appendRow H y h) n (by
        rw [appendRow_height]
        omega) :=
      ⟨theta, htheta⟩
    obtain ⟨q, hupdate⟩ :=
      Theta.exists_raw_predecessor H y h n hn
    refine ⟨q, htheta.1, ?_⟩
    intro a ha
    exact hupdate a ha
  · rintro ⟨q, hraw⟩
    exact isExactTrace_of_raw_candidate H y h n hn q theta hraw


end FiniteFatTree

end SMTree
end SuccessorTree
