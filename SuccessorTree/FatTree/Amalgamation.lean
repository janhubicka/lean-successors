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

/-- An infinite fat tree literally extends a finite stem when the
corresponding initial segment is equal to that stem. -/
def ExtendsStem (x : FiniteFatTree H) (W : FatTree H) : Prop :=
  W.initialSegment H x.height = x

/-- Membership in the manuscript basic open set `[x,U]`. -/
def InNeighborhood
    (x : FiniteFatTree H) (U W : FatTree H) : Prop :=
  FatTree.Reduces H W U ∧ ExtendsStem H x W

/-- Membership in `[n,U]`: refine `U` while keeping its first `n`
rows literally fixed. -/
def InDepthCone (n : Nat) (U V : FatTree H) : Prop :=
  FatTree.Reduces H V U ∧
    V.initialSegment H n = U.initialSegment H n

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

/-- A depth-cone refinement preserves which finite stems occur at
that depth. -/
theorem stemAt_of_depthCone
    {x : FiniteFatTree H} {U V : FatTree H} {n : Nat}
    (hx : StemAt H x U n)
    (hV : InDepthCone H n U V) :
    StemAt H x V n := by
  unfold StemAt at hx ⊢
  rw [hV.2]
  exact hx

/-- A member of a basic neighbourhood witnesses that the stem has
finite depth in the ambient fat tree. -/
theorem exists_stemAt_of_neighborhood
    {x : FiniteFatTree H} {U W : FatTree H}
    (hW : InNeighborhood H x U W) :
    ∃ n : Nat, StemAt H x U n := by
  rcases FiniteFatTree.exists_initialSegment_leFin_of_reduces
      H hW.1 x.height with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  unfold StemAt ExtendsStem at *
  rw [hW.2] at hn
  exact hn

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

/-- The finite stem is literally the initial segment of its splice,
not merely a finitary reduction of it. -/
theorem splice_initialSegment
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n) :
    (splice H x V n hcut).initialSegment H x.height = x := by
  apply FiniteFatTree.ext_data H rfl
  · apply heq_of_eq
    funext i
    change (splice H x V n hcut).cut i.1 = x.cut i
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
  · have hcuts :
        (splice H x V n hcut).initialSegment H x.height |>.cut =
          x.cut := by
      funext i
      change (splice H x V n hcut).cut i.1 = x.cut i
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
    cases hcuts
    apply heq_of_eq
    funext i
    change (splice H x V n hcut).row i.1 = x.row i
    exact eq_of_heq
      (splice_row_lt H x V n hcut i.2)

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
      (by simpa using hcut.symm) (by simpa using hi)]
    change U.cut i = U.cut (prefixTailIndex H w n m i)
    simp [prefixTailIndex, hi]
  · have hge : m ≤ i := Nat.le_of_not_gt hi
    rw [splice_cut_ge H (U.initialSegment H m) V n
      (by simpa using hcut.symm) (by simpa using hge)]
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
  · let ix : Fin m := ⟨i, hi⟩
    let hsplice :
        (U.initialSegment H m).terminalCut = V.cut n := by
      simpa using hcut.symm
    rw [splice_oneLift_lt H (U.initialSegment H m) V n
      hsplice (by simpa using hi)]
    rw [U.initialSegment_oneLift H m ix]
    rw [splice_cut_lt H (U.initialSegment H m) V n
      hsplice (by simpa using hi)]
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
      hsplice (by simpa using hge)]
    rw [splice_cut_ge H (U.initialSegment H m) V n
      hsplice (by simpa using hge)]
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
  · unfold ExtendsStem W
    exact splice_initialSegment H x V n hcut

end FatTree

end SMTree
end SuccessorTree
