import SuccessorTree.FatTree.Finitization

/-!
# Amalgamating a finite fat-tree prefix with an infinite tail

This file starts the A.3 layer.  The basic operation is the manuscript's
concatenation construction: replace the first selected block of an infinite
fat tree by a prescribed finite fat tree whose terminal cut matches a cut of
the tail.

No Ellentuck/EA assumption is used here.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A finite fat tree occurs at cut `n` of an infinite fat tree when it is
a finitary reduction of the first `n` rows.  This is the formal version of
the manuscript condition that the depth is `n`. -/
def StemAt (x : FiniteFatTree H) (U : FatTree H) (n : Nat) : Prop :=
  FiniteFatTree.LeFin H x (U.initialSegment H n)

/-- Exact finite-prefix agreement, expressed by the mathematical data
rather than equality of dependent records with proof fields.  This is the
Lean representation of saying that the first `x.height` rows of `W`
are literally the finite fat tree `x`. -/
def ExtendsStem (x : FiniteFatTree H) (W : FatTree H) : Prop :=
  (∀ i : Fin (x.height + 1), W.cut i.1 = x.cut i) ∧
  (∀ i : Fin x.height, HEq (W.row i.1) (x.row i))

/-- Membership in the manuscript basic open set `[x,U]`. -/
def InNeighborhood
    (x : FiniteFatTree H) (U W : FatTree H) : Prop :=
  FatTree.Reduces H W U ∧ ExtendsStem H x W

/-- Membership in `[n,U]`: refine `U` while keeping its first `n`
rows exactly fixed. -/
def InDepthCone (n : Nat) (U V : FatTree H) : Prop :=
  FatTree.Reduces H V U ∧
    ExtendsStem H (U.initialSegment H n) V

/-- Exact stem extension identifies every cut through the terminal cut. -/
theorem cut_eq_of_extendsStem
    {x : FiniteFatTree H} {W : FatTree H}
    (h : ExtendsStem H x W)
    (i : Fin (x.height + 1)) :
    W.cut i.1 = x.cut i :=
  h.1 i

/-- In particular, exact stem extension identifies the terminal cut. -/
theorem terminalCut_eq_of_extendsStem
    {x : FiniteFatTree H} {W : FatTree H}
    (h : ExtendsStem H x W) :
    W.cut x.height = x.terminalCut := by
  let last : Fin (x.height + 1) :=
    ⟨x.height, Nat.lt_succ_self x.height⟩
  have hlast : Fin.last x.height = last := Fin.ext rfl
  calc
    W.cut x.height = x.cut (Fin.last x.height) :=
      h.1 (Fin.last x.height)
    _ = x.cut last := by rw [hlast]
    _ = x.terminalCut := rfl

/-- The data-level prefix representation is exactly equivalent to the
literal finite initial-segment equality used in the manuscript. -/
theorem initialSegment_eq_of_extendsStem
    {x : FiniteFatTree H} {W : FatTree H}
    (h : ExtendsStem H x W) :
    W.initialSegment H x.height = x := by
  refine FiniteFatTree.ext_pointwise H
    (U := W.initialSegment H x.height) (V := x) rfl ?_ ?_
  · intro i
    change W.cut i.1 = x.cut i
    exact h.1 i
  · intro i
    change HEq (W.row i.1) (x.row i)
    exact h.2 i

/-- Literal finite-prefix equality gives the data-level stem predicate. -/
theorem extendsStem_of_initialSegment_eq
    {x : FiniteFatTree H} {W : FatTree H}
    (h : W.initialSegment H x.height = x) :
    ExtendsStem H x W := by
  subst x
  constructor
  · intro i
    rfl
  · intro i
    exact HEq.rfl

/-- A sufficiently deep cone refinement preserves every shorter literal
stem fixed by the ambient tree. -/
theorem extendsStem_of_depthCone
    {x : FiniteFatTree H} {A C : FatTree H} {q : Nat}
    (hxA : ExtendsStem H x A)
    (hC : InDepthCone H q A C)
    (hxq : x.height ≤ q) :
    ExtendsStem H x C := by
  have hCAq :
      C.initialSegment H q = A.initialSegment H q :=
    initialSegment_eq_of_extendsStem H hC.2
  have hCAx :
      C.initialSegment H x.height =
        A.initialSegment H x.height := by
    calc
      C.initialSegment H x.height =
          (C.initialSegment H q).initialSegment H x.height hxq :=
        (C.initialSegment_initialSegment H q x.height hxq).symm
      _ = (A.initialSegment H q).initialSegment H x.height hxq := by
        rw [hCAq]
      _ = A.initialSegment H x.height :=
        A.initialSegment_initialSegment H q x.height hxq
  have hAx :
      A.initialSegment H x.height = x :=
    initialSegment_eq_of_extendsStem H hxA
  exact extendsStem_of_initialSegment_eq H (hCAx.trans hAx)

/-- A stem occurring at cut `n` has terminal cut exactly `U.cut n`. -/
theorem terminalCut_eq_of_stemAt
    {x : FiniteFatTree H} {U : FatTree H} {n : Nat}
    (h : StemAt H x U n) :
    x.terminalCut = U.cut n := by
  simpa [StemAt] using h.2

/-- The cut index at which a finite stem occurs is unique. -/
theorem stemAt_unique
    {x : FiniteFatTree H} {U : FatTree H} {m n : Nat}
    (hm : StemAt H x U m) (hn : StemAt H x U n) :
    m = n := by
  apply U.cut_injective H
  calc
    U.cut m = x.terminalCut :=
      (terminalCut_eq_of_stemAt H hm).symm
    _ = U.cut n := terminalCut_eq_of_stemAt H hn

/-- Finite depth transports along an infinite fat-tree reduction. -/
theorem exists_stemAt_of_reduces
    {x : FiniteFatTree H} {V U : FatTree H} {n : Nat}
    (hx : StemAt H x V n)
    (hVU : FatTree.Reduces H V U) :
    ∃ m : Nat, StemAt H x U m := by
  rcases FiniteFatTree.exists_initialSegment_leFin_of_reduces
      H hVU n with ⟨m, hnm⟩
  refine ⟨m, ?_⟩
  unfold StemAt at hx ⊢
  exact FiniteFatTree.leFin_trans H hx hnm

/-- Transport a one-row approximation along an equality of its source
cut.  Keeping this transport explicit avoids asking Lean to eliminate a
heterogeneous equality between dependent approximation types. -/
def castRow {a b : Nat} (h : a = b) (u : AM H a 1) : AM H b 1 := by
  cases h
  exact u

@[simp] theorem castRow_rowEndLevel
    {a b : Nat} (h : a = b) (u : AM H a 1) :
    (castRow H h u).rowEndLevel H = u.rowEndLevel H := by
  cases h
  rfl

theorem castRow_heq
    {a b : Nat} (h : a = b) (u : AM H a 1) :
    HEq (castRow H h u) u := by
  cases h
  rfl

/-- Canonical extension is invariant under explicit transport of a
row along equality of its source cut. -/
@[simp] theorem canonicalExtension_castRow
    {a b : Nat} (h : a = b) (u : AM H a 1) :
    H.canonicalExtension ((castRow H h u).representative H) b =
      H.canonicalExtension (u.representative H) a := by
  cases h
  rfl

/-- Canonical extensions agree when both the source cut and the
finite row agree heterogeneously. -/
theorem canonicalExtension_eq_of_row_heq
    {a b : Nat} {u : AM H a 1} {v : AM H b 1}
    (hab : a = b) (huv : HEq u v) :
    H.canonicalExtension (u.representative H) a =
      H.canonicalExtension (v.representative H) b := by
  cases hab
  have huv' : u = v := eq_of_heq huv
  cases huv'
  rfl

/-- Exact stem agreement identifies the canonical row extensions. -/
theorem rowExtension_eq_of_extendsStem
    {x : FiniteFatTree H} {W : FatTree H}
    (h : ExtendsStem H x W)
    (i : Fin x.height) :
    W.rowExtension H i.1 = x.rowExtension H i := by
  unfold FatTree.rowExtension FiniteFatTree.rowExtension
  exact canonicalExtension_eq_of_row_heq H
    (h.1 i.castSucc) (h.2 i)

/-- Before the terminal cut, one-step Lift of an infinite tree extending
`x` agrees with one-step Lift in the finite stem. -/
theorem oneLift_eq_of_extendsStem
    {x : FiniteFatTree H} {W : FatTree H}
    (h : ExtendsStem H x W)
    (i : Fin x.height) (X : Set T) :
    W.oneLift H i.1 X = x.oneLift H i X := by
  unfold FatTree.oneLift FiniteFatTree.oneLift
  rw [rowExtension_eq_of_extendsStem H h i]

/-- Exact stem agreement gives the identity finite reduction from the stem
to the corresponding initial segment of the infinite tree. -/
theorem leFin_initialSegment_of_extendsStem
    {x : FiniteFatTree H} {W : FatTree H}
    (h : ExtendsStem H x W) :
    FiniteFatTree.LeFin H x (W.initialSegment H x.height) := by
  have hp := initialSegment_eq_of_extendsStem H h
  rw [hp]
  exact FiniteFatTree.leFin_refl H x

/-- A depth-cone refinement preserves which finite stems occur at
that depth. -/
theorem stemAt_of_depthCone
    {x : FiniteFatTree H} {U V : FatTree H} {n : Nat}
    (hx : StemAt H x U n)
    (hV : InDepthCone H n U V) :
    StemAt H x V n := by
  unfold StemAt at hx ⊢
  exact FiniteFatTree.leFin_trans H hx
    (leFin_initialSegment_of_extendsStem H hV.2)

/-- A member of a basic neighbourhood witnesses that the stem has
finite depth in the ambient fat tree. -/
theorem exists_stemAt_of_neighborhood
    {x : FiniteFatTree H} {U W : FatTree H}
    (hW : InNeighborhood H x U W) :
    ∃ n : Nat, StemAt H x U n := by
  rcases FiniteFatTree.exists_initialSegment_leFin_of_reduces
      H hW.1 x.height with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  unfold StemAt
  exact FiniteFatTree.leFin_trans H
    (leFin_initialSegment_of_extendsStem H hW.2) hn

/-- Splice a finite fat tree `x` onto the tail of an infinite fat tree
`V`, starting the tail at cut `n`.  The compatibility hypothesis is
exactly equality of the terminal cut of `x` with `V.cut n`. -/
def splice
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n) :
    FatTree H := by
  let c : Nat → Nat := fun i =>
    if hi : i < x.height then
      x.cut ⟨i, Nat.lt_succ_of_lt hi⟩
    else
      V.cut (n + (i - x.height))
  let r : (i : Nat) → AM H (c i) 1 := fun i => by
    by_cases hi : i < x.height
    · have hc :
          x.cut ⟨i, Nat.lt_succ_of_lt hi⟩ = c i := by
        simp [c, hi]
      exact castRow H hc (x.row ⟨i, hi⟩)
    · have hc :
          V.cut (n + (i - x.height)) = c i := by
        simp [c, hi]
      exact castRow H hc (V.row (n + (i - x.height)))
  refine {
    cut := c
    cut_zero := ?_
    row := r
    row_cut := ?_
  }
  · by_cases hpos : 0 < x.height
    · simpa [c, hpos] using x.cut_zero
    · have hh : x.height = 0 := Nat.eq_zero_of_not_pos hpos
      have hx0 : x.terminalCut = 0 := by
        unfold FiniteFatTree.terminalCut
        have hlast0 :
            Fin.last x.height =
              (0 : Fin (x.height + 1)) := by
          apply Fin.ext
          simpa [hh]
        calc
          x.cut (Fin.last x.height) = x.cut 0 :=
            congrArg x.cut hlast0
          _ = 0 := x.cut_zero
      have hv0 : V.cut n = 0 := hcut.symm.trans hx0
      simp [c, hpos, hv0]
  · intro i
    by_cases hi : i < x.height
    · let ix : Fin x.height := ⟨i, hi⟩
      have hend :
          (r i).rowEndLevel H =
            (x.row ix).rowEndLevel H := by
        simp [r, c, hi, ix, castRow_rowEndLevel]
      have hr := x.row_cut ix
      by_cases hnext : i + 1 < x.height
      · calc
          (r i).rowEndLevel H + 1 =
              (x.row ix).rowEndLevel H + 1 := by rw [hend]
          _ = x.cut ix.succ := hr
          _ = x.cut
              (⟨i + 1, Nat.lt_succ_of_lt hnext⟩ :
                Fin (x.height + 1)) :=
                congrArg x.cut (Fin.ext (by rfl))
          _ = c (i + 1) := by
                simp [c, hnext]
      · have heq : i + 1 = x.height := by omega
        have hlast :
            ix.succ = Fin.last x.height := by
          apply Fin.ext
          exact heq
        calc
          (r i).rowEndLevel H + 1 =
              (x.row ix).rowEndLevel H + 1 := by rw [hend]
          _ = x.cut ix.succ := hr
          _ = x.terminalCut := by
                unfold FiniteFatTree.terminalCut
                exact congrArg x.cut hlast
          _ = V.cut n := hcut
          _ = c (i + 1) := by
                simp [c, hnext, heq]
    · have hnext : ¬ i + 1 < x.height := by omega
      let q : Nat := n + (i - x.height)
      have hend :
          (r i).rowEndLevel H =
            (V.row q).rowEndLevel H := by
        simp [r, c, hi, q, castRow_rowEndLevel]
      have hq := V.row_cut q
      have hidx :
          n + (i + 1 - x.height) = q + 1 := by
        dsimp [q]
        omega
      calc
        (r i).rowEndLevel H + 1 =
            (V.row q).rowEndLevel H + 1 := by rw [hend]
        _ = V.cut (q + 1) := hq
        _ = c (i + 1) := by
              simp [c, hnext, q, hidx]


@[simp] theorem splice_cut_lt
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : i < x.height) :
    (splice H x V n hcut).cut i =
      x.cut ⟨i, Nat.lt_succ_of_lt hi⟩ := by
  simp [splice, hi]

@[simp] theorem splice_cut_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : x.height ≤ i) :
    (splice H x V n hcut).cut i =
      V.cut (n + (i - x.height)) := by
  have hnot : ¬ i < x.height := Nat.not_lt_of_ge hi
  simp [splice, hnot]

@[simp] theorem splice_cut_height
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n) :
    (splice H x V n hcut).cut x.height = V.cut n := by
  simpa using
    splice_cut_ge H x V n hcut (i := x.height) le_rfl

/-- Before the splice point, the row is the corresponding row of the
finite stem.  HEq records the definitional transport along the cut equality. -/
theorem splice_row_lt
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : i < x.height) :
    HEq ((splice H x V n hcut).row i)
      (x.row ⟨i, hi⟩) := by
  let ix : Fin x.height := ⟨i, hi⟩
  have hc :
      x.cut ix.castSucc = (splice H x V n hcut).cut i := by
    simpa [ix] using
      (splice_cut_lt H x V n hcut hi).symm
  have hcast :
      HEq (castRow H hc (x.row ix)) (x.row ix) :=
    castRow_heq H hc (x.row ix)
  simpa [splice, hi, ix] using hcast

/-- At and after the splice point, rows are the shifted rows of the infinite
tail. -/
theorem splice_row_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : x.height ≤ i) :
    HEq ((splice H x V n hcut).row i)
      (V.row (n + (i - x.height))) := by
  let q : Nat := n + (i - x.height)
  have hc :
      V.cut q = (splice H x V n hcut).cut i := by
    simpa [q] using
      (splice_cut_ge H x V n hcut hi).symm
  have hcast :
      HEq (castRow H hc (V.row q)) (V.row q) :=
    castRow_heq H hc (V.row q)
  have hnot : ¬ i < x.height := Nat.not_lt_of_ge hi
  simpa [splice, hnot, q] using hcast

/-- The splice agrees exactly with its prescribed finite stem on every
cut and row.  This is the data-level form of saying that the stem is the
initial segment of the splice. -/
theorem splice_extendsStem
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n) :
    ExtendsStem H x (splice H x V n hcut) := by
  constructor
  · intro i
    by_cases hi : i.1 < x.height
    · have h := splice_cut_lt H x V n hcut hi
      have hiEq :
          (⟨i.1, Nat.lt_succ_of_lt hi⟩ :
            Fin (x.height + 1)) = i := Fin.ext rfl
      simpa [hiEq] using h
    · have hieq : i.1 = x.height := by omega
      have hiLast : i = Fin.last x.height := by
        apply Fin.ext
        exact hieq
      calc
        (splice H x V n hcut).cut i.1 =
            V.cut n := by
              simpa [hieq] using
                splice_cut_height H x V n hcut
        _ = x.terminalCut := hcut.symm
        _ = x.cut i := by
              rw [hiLast]
              rfl
  · intro i
    exact splice_row_lt H x V n hcut i.2

/-- Before the splice point, the canonical row extension is exactly
the canonical extension of the corresponding finite stem row. -/
theorem splice_rowExtension_lt
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : i < x.height) :
    (splice H x V n hcut).rowExtension H i =
      x.rowExtension H ⟨i, hi⟩ := by
  let ix : Fin x.height := ⟨i, hi⟩
  unfold FatTree.rowExtension FiniteFatTree.rowExtension
  exact canonicalExtension_eq_of_row_heq H
    (splice_cut_lt H x V n hcut hi)
    (splice_row_lt H x V n hcut hi)

/-- At and after the splice point, the canonical row extension is the
corresponding shifted row extension of the tail. -/
theorem splice_rowExtension_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : x.height ≤ i) :
    (splice H x V n hcut).rowExtension H i =
      V.rowExtension H (n + (i - x.height)) := by
  unfold FatTree.rowExtension
  exact canonicalExtension_eq_of_row_heq H
    (splice_cut_ge H x V n hcut hi)
    (splice_row_ge H x V n hcut hi)

/-- One-step Lift before the splice is the one-step Lift of the finite stem. -/
theorem splice_oneLift_lt
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : i < x.height) (X : Set T) :
    (splice H x V n hcut).oneLift H i X =
      x.oneLift H ⟨i, hi⟩ X := by
  unfold FatTree.oneLift FiniteFatTree.oneLift
  rw [splice_rowExtension_lt H x V n hcut hi]

/-- One-step Lift at and after the splice is the shifted one-step Lift of
the infinite tail. -/
theorem splice_oneLift_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : x.height ≤ i) (X : Set T) :
    (splice H x V n hcut).oneLift H i X =
      V.oneLift H (n + (i - x.height)) X := by
  unfold FatTree.oneLift
  rw [splice_rowExtension_ge H x V n hcut hi]

/-- Once the starting row is at or beyond the splice point,
iterated Lift in the splice is exactly iterated Lift in the attached tail,
with the row index shifted by the splice offset. -/
theorem splice_liftSteps_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    (i steps : Nat) (hi : x.height ≤ i) (X : Set T) :
    (splice H x V n hcut).liftSteps H i steps X =
      V.liftSteps H (n + (i - x.height)) steps X := by
  induction steps generalizing i X with
  | zero =>
      rfl
  | succ steps ih =>
      rw [FatTree.liftSteps_succ, FatTree.liftSteps_succ]
      rw [splice_oneLift_ge H x V n hcut hi]
      have hi1 : x.height ≤ i + 1 := by omega
      have hidx :
          n + (i + 1 - x.height) =
            (n + (i - x.height)) + 1 := by
        omega
      have hrec :=
        ih (i := i + 1)
          (X := V.oneLift H (n + (i - x.height)) X)
          hi1
      simpa [hidx] using hrec

/-- Tail interval Lift in a splice agrees with interval Lift in the attached
tail, after shifting both endpoints. -/
theorem splice_liftTo_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    (a b : Nat) (ha : x.height ≤ a) (hab : a ≤ b)
    (X : Set T) :
    (splice H x V n hcut).liftTo H a b hab X =
      V.liftTo H
        (n + (a - x.height))
        (n + (b - x.height))
        (by
          have hb : x.height ≤ b := ha.trans hab
          omega) X := by
  have hb : x.height ≤ b := ha.trans hab
  have hdiff :
      (n + (b - x.height)) - (n + (a - x.height)) = b - a := by
    omega
  unfold FatTree.liftTo
  calc
    (splice H x V n hcut).liftSteps H a (b - a) X =
        V.liftSteps H (n + (a - x.height)) (b - a) X :=
      splice_liftSteps_ge H x V n hcut a (b - a) ha X
    _ = V.liftSteps H
        (n + (a - x.height))
        ((n + (b - x.height)) - (n + (a - x.height))) X := by
      rw [hdiff]

/-- Cut-index map for the reduction from a splice to its ambient tail.
Before the splice it follows the finite reduction witness; from the splice
cut onward it is the shifted identity on the tail. -/
def spliceIndex
    {x : FiniteFatTree H} {V : FatTree H} {n : Nat}
    (w : FiniteFatTree.ReductionWitness H x (V.initialSegment H n)) :
    Nat → Nat :=
  fun i =>
    if hi : i < x.height then
      (w.index (⟨i, by omega⟩ : Fin (x.height + 1))).1
    else
      n + (i - x.height)

/-- The splice-index map is strictly increasing when the finite witness
preserves the common terminal cut. -/
theorem spliceIndex_strict
    {x : FiniteFatTree H} {V : FatTree H} {n : Nat}
    (w : FiniteFatTree.ReductionWitness H x (V.initialSegment H n))
    (hterm : x.terminalCut = (V.initialSegment H n).terminalCut) :
    StrictMono (spliceIndex H w) := by
  have hlast :=
    w.index_last_eq_last H hterm
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hi : i < x.height
  · by_cases hnext : i + 1 < x.height
    · let a : Fin (x.height + 1) := ⟨i, by omega⟩
      let b : Fin (x.height + 1) := ⟨i + 1, by omega⟩
      have hab : a < b := by
        exact Fin.lt_def.mpr (by
          change i < i + 1
          omega)
      have hw := w.index_strict hab
      change (w.index a).1 < (w.index b).1 at hw
      simpa [spliceIndex, hi, hnext, a, b] using hw
    · have heq : i + 1 = x.height := by omega
      let a : Fin (x.height + 1) := ⟨i, by omega⟩
      have halast : a < Fin.last x.height := by
        exact Fin.lt_def.mpr (by
          change i < x.height
          exact hi)
      have hw := w.index_strict halast
      have hwval :
          (w.index a).1 < n := by
        rw [hlast] at hw
        exact hw
      simpa [spliceIndex, hi, hnext, heq, a] using hwval
  · have hge : x.height ≤ i := Nat.le_of_not_gt hi
    have hnext : ¬ i + 1 < x.height := by omega
    simp [spliceIndex, hi, hnext]
    omega

/-- The splice-index map sends every splice cut to the corresponding cut of
the ambient tail. -/
theorem splice_cut_eq_index
    {x : FiniteFatTree H} {V : FatTree H} {n : Nat}
    (hcut : x.terminalCut = V.cut n)
    (w : FiniteFatTree.ReductionWitness H x (V.initialSegment H n))
    (i : Nat) :
    (splice H x V n hcut).cut i =
      V.cut (spliceIndex H w i) := by
  by_cases hi : i < x.height
  · let a : Fin (x.height + 1) := ⟨i, by omega⟩
    have hw := w.cut_eq a
    change
      x.cut a =
        V.cut (w.index a).1 at hw
    simpa [spliceIndex, hi, a] using hw
  · have hge : x.height ≤ i := Nat.le_of_not_gt hi
    rw [splice_cut_ge H x V n hcut hge]
    simp [spliceIndex, hi]

/-- Before the splice point, the next splice index agrees with the
next index of the finite reduction witness, including the boundary row. -/
theorem spliceIndex_succ_eq_of_lt
    {x : FiniteFatTree H} {V : FatTree H} {n : Nat}
    (w : FiniteFatTree.ReductionWitness H x (V.initialSegment H n))
    (hterm : x.terminalCut = (V.initialSegment H n).terminalCut)
    {i : Nat} (hi : i < x.height) :
    spliceIndex H w (i + 1) =
      (w.index ((⟨i, hi⟩ : Fin x.height).succ)).1 := by
  let ix : Fin x.height := ⟨i, hi⟩
  by_cases hnext : i + 1 < x.height
  · let j : Fin (x.height + 1) := ⟨i + 1, by omega⟩
    have hj : j = ix.succ := Fin.ext rfl
    calc
      spliceIndex H w (i + 1) = (w.index j).1 := by
        simp [spliceIndex, hnext, j]
      _ = (w.index ix.succ).1 := by rw [hj]
  · have heq : i + 1 = x.height := by omega
    have hixlast : ix.succ = Fin.last x.height := by
      apply Fin.ext
      exact heq
    have hlast := w.index_last_eq_last H hterm
    have hval : (w.index ix.succ).1 = n := by
      rw [hixlast, hlast]
      rfl
    have hleft : spliceIndex H w (i + 1) = n := by
      simp [spliceIndex, hnext, heq]
    exact hleft.trans hval.symm

/-- Splicing a finite stem occurring at cut `n` onto the tail of `V`
produces an infinite fat subtree of `V`.  This is the structural
concatenation lemma used in A3(1). -/
theorem splice_reduces
    {x : FiniteFatTree H} {V : FatTree H} {n : Nat}
    (hstem : StemAt H x V n) :
    FatTree.Reduces H
      (splice H x V n (terminalCut_eq_of_stemAt H hstem)) V := by
  let hcut : x.terminalCut = V.cut n :=
    terminalCut_eq_of_stemAt H hstem
  rcases hstem.1 with ⟨w⟩
  have hterm :
      x.terminalCut = (V.initialSegment H n).terminalCut := hstem.2
  have hstrict : StrictMono (spliceIndex H w) :=
    spliceIndex_strict H w hterm
  refine ⟨{
    index := spliceIndex H w
    index_strict := hstrict
    cut_eq := splice_cut_eq_index H hcut w
    lift_subset := ?_
  }⟩
  intro i
  by_cases hi : i < x.height
  · let ix : Fin x.height := ⟨i, hi⟩
    have hw := w.lift_subset ix
    rw [V.initialSegment_liftTo H n] at hw
    rw [V.initialSegment_cut H n (w.index ix.castSucc)] at hw
    have h0 :
        spliceIndex H w i = (w.index ix.castSucc).1 := by
      simp [spliceIndex, hi, ix]
    have h1 :
        spliceIndex H w (i + 1) = (w.index ix.succ).1 :=
      spliceIndex_succ_eq_of_lt H w hterm hi
    rw [splice_oneLift_lt H x V n hcut hi]
    rw [splice_cut_lt H x V n hcut hi]
    change
      x.oneLift H ix
          (TreeLevel (T := T) (x.cut ix.castSucc)) ⊆
        V.liftTo H
          (spliceIndex H w i)
          (spliceIndex H w (i + 1))
          _
          (TreeLevel (T := T) (V.cut (spliceIndex H w i)))
    have habw :
        (w.index ix.castSucc).1 ≤ (w.index ix.succ).1 :=
      Nat.le_of_lt (w.index_strict (by
        exact Fin.lt_def.mpr (by
          change i < i + 1
          omega)))
    have hsp :
        spliceIndex H w i ≤ spliceIndex H w (i + 1) :=
      Nat.le_of_lt (hstrict (Nat.lt_succ_self i))
    have htarget :=
      V.liftTo_level_congr H habw hsp h0.symm h1.symm
    intro z hz
    have hz' := hw hz
    rw [htarget] at hz'
    exact hz'
  · have hge : x.height ≤ i := Nat.le_of_not_gt hi
    have hge1 : x.height ≤ i + 1 := by omega
    let q : Nat := n + (i - x.height)
    have h0 : spliceIndex H w i = q := by
      simp [spliceIndex, hi, q]
    have hnot1 : ¬ i + 1 < x.height := Nat.not_lt_of_ge hge1
    have h1 : spliceIndex H w (i + 1) = q + 1 := by
      simp [spliceIndex, hnot1, q]
      omega
    rw [splice_oneLift_ge H x V n hcut hge]
    rw [splice_cut_ge H x V n hcut hge]
    have hsp :
        spliceIndex H w i ≤ spliceIndex H w (i + 1) :=
      Nat.le_of_lt (hstrict (Nat.lt_succ_self i))
    have htarget :=
      V.liftTo_level_congr H (by omega) hsp h0.symm h1.symm
    rw [← htarget]
    rw [V.liftTo_succ H q
      (TreeLevel (T := T) (V.cut q))]

/-- If a reduction witness hits the same ambient cut at source index
`n` and ambient index `m`, then its index map sends `n` to `m`. -/
theorem reduction_index_eq_of_cut_eq
    {V U : FatTree H}
    (w : FatTree.ReductionWitness H V U)
    {n m : Nat} (hcut : V.cut n = U.cut m) :
    w.index n = m := by
  apply U.cut_injective H
  calc
    U.cut (w.index n) = V.cut n := (w.cut_eq n).symm
    _ = U.cut m := hcut

/-- Index map for the splice consisting of the first `m` rows of `U`
followed by the tail of a reduction `V ≤ U` starting at row `n`. -/
def prefixTailIndex
    {V U : FatTree H}
    (w : FatTree.ReductionWitness H V U)
    (n m : Nat) : Nat → Nat :=
  fun i =>
    if hi : i < m then i
    else w.index (n + (i - m))

/-- The prefix-tail index is strictly increasing once the common splice cut
is aligned by the original reduction witness. -/
theorem prefixTailIndex_strict
    {V U : FatTree H}
    (w : FatTree.ReductionWitness H V U)
    {n m : Nat} (hnm : w.index n = m) :
    StrictMono (prefixTailIndex H w n m) := by
  apply strictMono_nat_of_lt_succ
  intro i
  by_cases hi : i < m
  · by_cases hnext : i + 1 < m
    · simp [prefixTailIndex, hi, hnext]
    · have heq : i + 1 = m := by omega
      have hnot : ¬ i + 1 < m := hnext
      calc
        prefixTailIndex H w n m i = i := by
          simp [prefixTailIndex, hi]
        _ < m := hi
        _ = w.index n := hnm.symm
        _ = prefixTailIndex H w n m (i + 1) := by
          simp [prefixTailIndex, hnot, heq]
  · have hge : m ≤ i := Nat.le_of_not_gt hi
    have hnext : ¬ i + 1 < m := by omega
    let q : Nat := n + (i - m)
    have hq : n + (i + 1 - m) = q + 1 := by
      dsimp [q]
      omega
    have hw := w.index_strict (Nat.lt_succ_self q)
    simpa [prefixTailIndex, hi, hnext, q, hq] using hw

/-- Cut alignment for the ambient-prefix/reduced-tail splice. -/
theorem prefixTail_cut_eq
    {V U : FatTree H}
    (w : FatTree.ReductionWitness H V U)
    {n m : Nat} (hcut : V.cut n = U.cut m)
    (i : Nat) :
    (splice H (U.initialSegment H m) V n
      (by simpa using hcut.symm)).cut i =
      U.cut (prefixTailIndex H w n m i) := by
  by_cases hi : i < m
  · rw [splice_cut_lt H (U.initialSegment H m) V n
      (by simpa using hcut.symm) (by
        change i < m
        exact hi)]
    change U.cut i = U.cut (prefixTailIndex H w n m i)
    simp [prefixTailIndex, hi]
  · have hge : m ≤ i := Nat.le_of_not_gt hi
    rw [splice_cut_ge H (U.initialSegment H m) V n
      (by simpa using hcut.symm) (by
        change m ≤ i
        exact hge)]
    let q : Nat := n + (i - m)
    have hw := w.cut_eq q
    change V.cut q = U.cut (prefixTailIndex H w n m i)
    rw [hw]
    simp [prefixTailIndex, hi, q]

/-- Keeping the first `m` rows of `U` and then attaching the tail of a
reduction `V ≤ U` at a common cut again gives a reduction of `U`.
This is the structural construction used in A3(2). -/
theorem splice_prefix_tail_reduces
    {V U : FatTree H}
    (hVU : FatTree.Reduces H V U)
    {n m : Nat} (hcut : V.cut n = U.cut m) :
    FatTree.Reduces H
      (splice H (U.initialSegment H m) V n
        (by simpa using hcut.symm)) U := by
  rcases hVU with ⟨w⟩
  have hnm : w.index n = m :=
    reduction_index_eq_of_cut_eq H w hcut
  have hstrict : StrictMono (prefixTailIndex H w n m) :=
    prefixTailIndex_strict H w hnm
  refine ⟨{
    index := prefixTailIndex H w n m
    index_strict := hstrict
    cut_eq := prefixTail_cut_eq H w hcut
    lift_subset := ?_
  }⟩
  intro i
  by_cases hi : i < m
  · let ix :
        Fin ((U.initialSegment H m).height) :=
      ⟨i, by
        change i < m
        exact hi⟩
    let hsplice :
        (U.initialSegment H m).terminalCut = V.cut n := by
      simpa using hcut.symm
    rw [splice_oneLift_lt H (U.initialSegment H m) V n
      hsplice ix.2]
    rw [U.initialSegment_oneLift H m ix]
    rw [splice_cut_lt H (U.initialSegment H m) V n
      hsplice ix.2]
    change
      U.oneLift H i (TreeLevel (T := T) (U.cut i)) ⊆
        U.liftTo H
          (prefixTailIndex H w n m i)
          (prefixTailIndex H w n m (i + 1))
          _
          (TreeLevel (T := T)
            (U.cut (prefixTailIndex H w n m i)))
    have h0 : prefixTailIndex H w n m i = i := by
      simp [prefixTailIndex, hi]
    have h1 : prefixTailIndex H w n m (i + 1) = i + 1 := by
      by_cases hnext : i + 1 < m
      · simp [prefixTailIndex, hnext]
      · have heq : i + 1 = m := by omega
        simp [prefixTailIndex, hnext, heq, hnm]
    have hsp :
        prefixTailIndex H w n m i ≤
          prefixTailIndex H w n m (i + 1) :=
      Nat.le_of_lt (hstrict (Nat.lt_succ_self i))
    have htarget :=
      U.liftTo_level_congr H (by omega) hsp h0.symm h1.symm
    rw [← htarget]
    rw [U.liftTo_succ H i
      (TreeLevel (T := T) (U.cut i))]
  · have hge : m ≤ i := Nat.le_of_not_gt hi
    let q : Nat := n + (i - m)
    have hnext : ¬ i + 1 < m := by omega
    have hq : n + (i + 1 - m) = q + 1 := by
      dsimp [q]
      omega
    let hsplice :
        (U.initialSegment H m).terminalCut = V.cut n := by
      simpa using hcut.symm
    rw [splice_oneLift_ge H (U.initialSegment H m) V n
      hsplice (by
        change m ≤ i
        exact hge)]
    rw [splice_cut_ge H (U.initialSegment H m) V n
      hsplice (by
        change m ≤ i
        exact hge)]
    have hw := w.lift_subset q
    have h0 :
        prefixTailIndex H w n m i = w.index q := by
      simp [prefixTailIndex, hi, q]
    have h1 :
        prefixTailIndex H w n m (i + 1) = w.index (q + 1) := by
      simp [prefixTailIndex, hnext, q, hq]
    have habw : w.index q ≤ w.index (q + 1) :=
      Nat.le_of_lt (w.index_strict (Nat.lt_succ_self q))
    have hsp :
        prefixTailIndex H w n m i ≤
          prefixTailIndex H w n m (i + 1) :=
      Nat.le_of_lt (hstrict (Nat.lt_succ_self i))
    have htarget :=
      U.liftTo_level_congr H habw hsp h0.symm h1.symm
    intro z hz
    have hz' := hw hz
    rw [htarget] at hz'
    exact hz'

/-- Any refinement of a splice which literally starts with the common
stem `x` can be rebased into the attached tail.  This is the key
neighbourhood-inclusion lemma for A3(2). -/
theorem neighborhood_reduces_attached_tail
    {x p : FiniteFatTree H} {V W : FatTree H} {n : Nat}
    (hpV : p.terminalCut = V.cut n)
    (hxV : StemAt H x V n)
    (hxp : x.terminalCut = p.terminalCut)
    (hW : InNeighborhood H x (splice H p V n hpV) W) :
    FatTree.Reduces H W V := by
  rcases hxV.1 with ⟨a⟩
  rcases hW.1 with ⟨b⟩
  have haLast :=
    a.index_last_eq_last H hxV.2
  have hbAt : b.index x.height = p.height := by
    apply (splice H p V n hpV).cut_injective H
    calc
      (splice H p V n hpV).cut (b.index x.height) =
          W.cut x.height := (b.cut_eq x.height).symm
      _ = x.terminalCut :=
        terminalCut_eq_of_extendsStem H hW.2
      _ = p.terminalCut := hxp
      _ = (splice H p V n hpV).cut p.height := by
        calc
          p.terminalCut = V.cut n := hpV
          _ = (splice H p V n hpV).cut p.height :=
            (splice_cut_height H p V n hpV).symm
  let β : Nat → Nat := fun j =>
    if hj : j < x.height then
      (a.index (⟨j, by omega⟩ : Fin (x.height + 1))).1
    else
      n + (b.index j - p.height)
  have hβstrict : StrictMono β := by
    apply strictMono_nat_of_lt_succ
    intro j
    by_cases hj : j < x.height
    · by_cases hnext : j + 1 < x.height
      · let ja : Fin (x.height + 1) := ⟨j, by omega⟩
        let jb : Fin (x.height + 1) := ⟨j + 1, by omega⟩
        have hab : ja < jb := Fin.lt_def.mpr (by
          change j < j + 1
          exact Nat.lt_succ_self j)
        have ha := a.index_strict hab
        change (a.index ja).1 < (a.index jb).1 at ha
        simpa [β, hj, hnext, ja, jb] using ha
      · have heq : j + 1 = x.height := by omega
        let ja : Fin (x.height + 1) := ⟨j, by omega⟩
        have hjaLast : ja < Fin.last x.height :=
          Fin.lt_def.mpr (by
            change j < x.height
            exact hj)
        have ha := a.index_strict hjaLast
        have haVal :
            (a.index ja).1 <
              (a.index (Fin.last x.height)).1 := by
          exact ha
        have hlastVal :
            (a.index (Fin.last x.height)).1 = n := by
          rw [haLast]
          rfl
        have haval : (a.index ja).1 < n := by
          omega
        have hbzero : b.index (j + 1) = p.height := by
          rw [heq]
          exact hbAt
        calc
          β j = (a.index ja).1 := by simp [β, hj, ja]
          _ < n := haval
          _ = n + (b.index (j + 1) - p.height) := by
            rw [hbzero]
            simp
          _ = β (j + 1) := by
            simp [β, hnext]
    · have hge : x.height ≤ j := Nat.le_of_not_gt hj
      have hnext : ¬ j + 1 < x.height := by omega
      have hbj : p.height ≤ b.index j := by
        rw [← hbAt]
        exact b.index_strict.monotone hge
      have hb : b.index j < b.index (j + 1) :=
        b.index_strict (Nat.lt_succ_self j)
      have hbj1 : p.height ≤ b.index (j + 1) :=
        hbj.trans (Nat.le_of_lt hb)
      have hsub :
          b.index j - p.height <
            b.index (j + 1) - p.height := by
        omega
      calc
        β j = n + (b.index j - p.height) := by
          simp [β, hj]
        _ < n + (b.index (j + 1) - p.height) :=
          Nat.add_lt_add_left hsub n
        _ = β (j + 1) := by
          simp [β, hnext]
  have hβstep : ∀ j : Nat, β j < β (j + 1) := fun j =>
    hβstrict (Nat.lt_succ_self j)
  refine ⟨{
    index := β
    index_strict := hβstrict
    cut_eq := ?_
    lift_subset := ?_
  }⟩
  · intro j
    by_cases hj : j < x.height
    · let ja : Fin (x.height + 1) := ⟨j, by omega⟩
      have hWcut :=
        cut_eq_of_extendsStem H hW.2 ja
      have hacut := a.cut_eq ja
      change x.cut ja = V.cut (a.index ja).1 at hacut
      calc
        W.cut j = x.cut ja := hWcut
        _ = V.cut (a.index ja).1 := hacut
        _ = V.cut (β j) := by simp [β, hj, ja]
    · have hge : x.height ≤ j := Nat.le_of_not_gt hj
      have hbj : p.height ≤ b.index j := by
        rw [← hbAt]
        exact b.index_strict.monotone hge
      have hbcut := b.cut_eq j
      calc
        W.cut j =
            (splice H p V n hpV).cut (b.index j) := hbcut
        _ = V.cut (n + (b.index j - p.height)) :=
          splice_cut_ge H p V n hpV hbj
        _ = V.cut (β j) := by simp [β, hj]
  · intro j
    by_cases hj : j < x.height
    · let ji : Fin x.height := ⟨j, hj⟩
      have haLift := a.lift_subset ji
      rw [V.initialSegment_liftTo H n] at haLift
      rw [V.initialSegment_cut H n (a.index ji.castSucc)] at haLift
      rw [oneLift_eq_of_extendsStem H hW.2 ji]
      have hWcutj : W.cut j = x.cut ji.castSucc := by
        simpa [ji] using
          cut_eq_of_extendsStem H hW.2 ji.castSucc
      rw [hWcutj]
      have h0 : β j = (a.index ji.castSucc).1 := by
        simp [β, hj, ji]
      have h1 : β (j + 1) = (a.index ji.succ).1 := by
        by_cases hnext : j + 1 < x.height
        · let jj : Fin (x.height + 1) := ⟨j + 1, by omega⟩
          have hjj : jj = ji.succ := Fin.ext rfl
          calc
            β (j + 1) = (a.index jj).1 := by
              simp [β, hnext, jj]
            _ = (a.index ji.succ).1 := by rw [hjj]
        · have heq : j + 1 = x.height := by omega
          have hjiLast : ji.succ = Fin.last x.height := by
            apply Fin.ext
            exact heq
          have hlastVal :
              (a.index (Fin.last x.height)).1 = n := by
            rw [haLast]
            rfl
          have haval : (a.index ji.succ).1 = n := by
            rw [hjiLast]
            exact hlastVal
          have hbzero : b.index (j + 1) = p.height := by
            rw [heq]
            exact hbAt
          calc
            β (j + 1) =
                n + (b.index (j + 1) - p.height) := by
                  simp [β, hnext]
            _ = n := by rw [hbzero]; simp
            _ = (a.index ji.succ).1 := haval.symm
      have haa :
          (a.index ji.castSucc).1 ≤ (a.index ji.succ).1 :=
        Nat.le_of_lt (a.index_strict
          (Fin.lt_def.mpr (by
            change j < j + 1
            exact Nat.lt_succ_self j)))
      have hβ :
          β j ≤ β (j + 1) :=
        Nat.le_of_lt (hβstep j)
      have htarget :=
        V.liftTo_level_congr H haa hβ h0.symm h1.symm
      intro z hz
      have hz' := haLift hz
      rw [htarget] at hz'
      exact hz'
    · have hge : x.height ≤ j := Nat.le_of_not_gt hj
      have hnext : ¬ j + 1 < x.height := by omega
      have hbj : p.height ≤ b.index j := by
        rw [← hbAt]
        exact b.index_strict.monotone hge
      have hbmono :
          b.index j ≤ b.index (j + 1) :=
        Nat.le_of_lt (b.index_strict (Nat.lt_succ_self j))
      have hbj1 : p.height ≤ b.index (j + 1) :=
        hbj.trans hbmono
      have hbLift := b.lift_subset j
      have htail :=
        splice_liftTo_ge H p V n hpV
          (b.index j) (b.index (j + 1))
          hbj hbmono
          (TreeLevel (T := T)
            ((splice H p V n hpV).cut (b.index j)))
      rw [htail] at hbLift
      rw [splice_cut_ge H p V n hpV hbj] at hbLift
      have h0 :
          β j = n + (b.index j - p.height) := by
        simp [β, hj]
      have h1 :
          β (j + 1) =
            n + (b.index (j + 1) - p.height) := by
        simp [β, hnext]
      have hsrc :
          n + (b.index j - p.height) ≤
            n + (b.index (j + 1) - p.height) := by
        omega
      have hβ :
          β j ≤ β (j + 1) :=
        Nat.le_of_lt (hβstep j)
      have htarget :=
        V.liftTo_level_congr H hsrc hβ h0.symm h1.symm
      intro z hz
      have hz' := hbLift hz
      rw [htarget] at hz'
      exact hz'

/-- Todorčević A3(1) for the fat-tree space: every depth-cone refinement
contains an infinite fat tree extending the prescribed finite stem. -/
theorem a3_one_nonempty
    {x : FiniteFatTree H} {U V : FatTree H} {n : Nat}
    (hx : StemAt H x U n)
    (hV : InDepthCone H n U V) :
    ∃ W : FatTree H, InNeighborhood H x V W := by
  have hxV : StemAt H x V n :=
    stemAt_of_depthCone H hx hV
  let hcut : x.terminalCut = V.cut n :=
    terminalCut_eq_of_stemAt H hxV
  let W : FatTree H := splice H x V n hcut
  refine ⟨W, ?_, ?_⟩
  · exact splice_reduces H hxV
  · exact splice_extendsStem H x V n hcut

/-- Todorčević A3(2) for the fat-tree space.

If `V ≤ U` and `[x,V]` is nonempty, there is a refinement `U'` which
keeps the prefix of `U` through the depth of `x`, has nonempty
`[x,U']`, and whose `x`-neighbourhood is contained in `[x,V]`. -/
theorem a3_two_amalgamation
    {x : FiniteFatTree H} {V U : FatTree H}
    (hVU : FatTree.Reduces H V U)
    (hne : ∃ W : FatTree H, InNeighborhood H x V W) :
    ∃ (m : Nat) (U' : FatTree H),
      StemAt H x U m ∧
      InDepthCone H m U U' ∧
      (∃ W : FatTree H, InNeighborhood H x U' W) ∧
      (∀ W : FatTree H,
        InNeighborhood H x U' W →
          InNeighborhood H x V W) := by
  rcases hne with ⟨W₀, hW₀⟩
  rcases exists_stemAt_of_neighborhood H hW₀ with
    ⟨n, hxV⟩
  rcases exists_stemAt_of_reduces H hxV hVU with
    ⟨m, hxU⟩
  have hcut : V.cut n = U.cut m := by
    calc
      V.cut n = x.terminalCut :=
        (terminalCut_eq_of_stemAt H hxV).symm
      _ = U.cut m :=
        terminalCut_eq_of_stemAt H hxU
  let p : FiniteFatTree H := U.initialSegment H m
  have hpV : p.terminalCut = V.cut n := by
    dsimp [p]
    simpa using hcut.symm
  let U' : FatTree H := splice H p V n hpV
  have hU'reduces : FatTree.Reduces H U' U := by
    dsimp [U']
    exact splice_prefix_tail_reduces H hVU hcut
  have hU'prefix :
      ExtendsStem H (U.initialSegment H m) U' := by
    dsimp [U', p]
    exact splice_extendsStem H (U.initialSegment H m) V n hpV
  have hdepth : InDepthCone H m U U' :=
    ⟨hU'reduces, hU'prefix⟩
  have hnonempty :
      ∃ W : FatTree H, InNeighborhood H x U' W :=
    a3_one_nonempty H hxU hdepth
  refine ⟨m, U', hxU, hdepth, hnonempty, ?_⟩
  intro W hWU'
  have hxp : x.terminalCut = p.terminalCut := by
    exact hxU.2
  have hWV : FatTree.Reduces H W V := by
    dsimp [U'] at hWU'
    exact neighborhood_reduces_attached_tail H
      hpV hxV hxp hWU'
  exact ⟨hWV, hWU'.2⟩

end FatTree

end SMTree
end SuccessorTree
