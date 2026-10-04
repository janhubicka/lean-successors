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
          c i = x.cut ⟨i, Nat.lt_succ_of_lt hi⟩ := by
        simp [c, hi]
      rw [hc]
      exact x.row ⟨i, hi⟩
    · have hc :
          c i = V.cut (n + (i - x.height)) := by
        simp [c, hi]
      rw [hc]
      exact V.row (n + (i - x.height))
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
        subst hh
        simpa [FiniteFatTree.terminalCut] using x.cut_zero
      have hv0 : V.cut n = 0 := hcut.symm.trans hx0
      simp [c, hpos, hv0]
  · intro i
    by_cases hi : i < x.height
    · let ix : Fin x.height := ⟨i, hi⟩
      have hr := x.row_cut ix
      by_cases hnext : i + 1 < x.height
      · have hs :
            ix.succ =
              (⟨i + 1, Nat.lt_succ_of_lt hnext⟩ :
                Fin (x.height + 1)) := Fin.ext rfl
        rw [hs] at hr
        simpa [r, c, hi, hnext, ix] using hr
      · have heq : i + 1 = x.height := by omega
        have hs :
            ix.succ =
              (⟨x.height, Nat.lt_succ_self x.height⟩ :
                Fin (x.height + 1)) := by
          apply Fin.ext
          exact heq
        have hprefix :
            (r i).rowEndLevel H + 1 = x.terminalCut := by
          rw [← hs]
          simpa [r, c, hi, ix] using hr
        calc
          (r i).rowEndLevel H + 1 = x.terminalCut := hprefix
          _ = V.cut n := hcut
          _ = c (i + 1) := by
            simp [c, hnext, heq]
    · have hnext : ¬ i + 1 < x.height := by omega
      let q : Nat := n + (i - x.height)
      have hq := V.row_cut q
      have hidx :
          n + (i + 1 - x.height) = q + 1 := by
        dsimp [q]
        omega
      simpa [r, c, hi, hnext, q, hidx] using hq

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
  simp [splice, hi]

/-- At and after the splice point, rows are the shifted rows of the infinite
tail. -/
theorem splice_row_ge
    (x : FiniteFatTree H) (V : FatTree H) (n : Nat)
    (hcut : x.terminalCut = V.cut n)
    {i : Nat} (hi : x.height ≤ i) :
    HEq ((splice H x V n hcut).row i)
      (V.row (n + (i - x.height))) := by
  have hnot : ¬ i < x.height := Nat.not_lt_of_ge hi
  simp [splice, hnot]

end FatTree

end SMTree
end SuccessorTree
