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

end FatTree

end SMTree
end SuccessorTree
