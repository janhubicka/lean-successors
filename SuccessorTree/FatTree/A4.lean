import SuccessorTree.FatTree.ApproximationSystem
import SuccessorTree.ShapeLocalPigeonhole

/-!
# The A4 one-step bridge for fat trees

This file begins the formalization of Todorčević A4 for the fat-tree
approximation space.  The first layer is deliberately finite: adjoining one
row to a finite fat tree, and recovering that row from a one-step extension.

The later trace/fusion layer will use this bridge to transfer colourings of
finite fat-tree approximations to colourings of one-row shape maps.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FiniteFatTree

variable (H : SMTree S)

/-- Natural-number cut function for adjoining one row to a finite fat tree. -/
private def appendCut
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1)
    (i : Nat) : Nat :=
  if hi : i ≤ x.height then
    x.cut ⟨i, by omega⟩
  else
    g.rowEndLevel H + 1

@[simp] private theorem appendCut_old
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1)
    {i : Nat} (hi : i ≤ x.height) :
    appendCut H x g i = x.cut ⟨i, by omega⟩ := by
  simp [appendCut, hi]

@[simp] private theorem appendCut_new
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    appendCut H x g (x.height + 1) = g.rowEndLevel H + 1 := by
  simp [appendCut]

/-- Append one admissible one-row approximation after a finite fat tree. -/
noncomputable def appendRow
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    FiniteFatTree H := by
  let c : Nat → Nat := appendCut H x g
  let r : (i : Fin (x.height + 1)) → AM H (c i.1) 1 := fun i => by
    by_cases hi : i.1 < x.height
    · let j : Fin x.height := ⟨i.1, hi⟩
      have hc :
          x.cut j.castSucc = c i.1 := by
        simp [c, appendCut, Nat.le_of_lt hi, j]
      exact FatTree.castRow H hc (x.row j)
    · have hieq : i.1 = x.height := by omega
      have hc :
          x.terminalCut = c i.1 := by
        subst hieq
        simp [c, appendCut, FiniteFatTree.terminalCut]
      exact FatTree.castRow H hc g
  refine {
    height := x.height + 1
    cut := fun i => c i.1
    cut_zero := ?_
    row := r
    row_cut := ?_
  }
  · simp [c, appendCut, x.cut_zero]
  · intro i
    by_cases hi : i.1 < x.height
    · let j : Fin x.height := ⟨i.1, hi⟩
      have hend :
          (r i).rowEndLevel H = (x.row j).rowEndLevel H := by
        simp [r, hi, j, FatTree.castRow_rowEndLevel]
      have hr := x.row_cut j
      have hsucc :
          j.succ =
            (⟨i.1 + 1, by omega⟩ : Fin (x.height + 1)) :=
        Fin.ext rfl
      calc
        (r i).rowEndLevel H + 1 =
            (x.row j).rowEndLevel H + 1 := by rw [hend]
        _ = x.cut j.succ := hr
        _ = x.cut ⟨i.1 + 1, by omega⟩ := by rw [hsucc]
        _ = c (i.1 + 1) := by
          symm
          simp [c, appendCut, show i.1 + 1 ≤ x.height by omega]
        _ = c i.succ.1 := by rfl
    · have hieq : i.1 = x.height := by omega
      have hend :
          (r i).rowEndLevel H = g.rowEndLevel H := by
        simp [r, hi, hieq, FatTree.castRow_rowEndLevel]
      calc
        (r i).rowEndLevel H + 1 =
            g.rowEndLevel H + 1 := by rw [hend]
        _ = c (x.height + 1) := by
          simp [c, appendCut]
        _ = c i.succ.1 := by
          congr
          omega

@[simp] theorem appendRow_height
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    (appendRow H x g).height = x.height + 1 := rfl

/-- All old cuts are unchanged by appending one row. -/
theorem appendRow_cut_old
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1)
    (i : Fin (x.height + 1)) :
    (appendRow H x g).cut i.castSucc = x.cut i := by
  change appendCut H x g i.1 = x.cut i
  have hi : i.1 ≤ x.height := Nat.le_of_lt_succ i.2
  simpa using appendCut_old H x g hi

/-- The new terminal cut is one above the last image level of the appended
row. -/
@[simp] theorem appendRow_terminalCut
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    (appendRow H x g).terminalCut = g.rowEndLevel H + 1 := by
  unfold terminalCut
  change appendCut H x g (x.height + 1) = _
  exact appendCut_new H x g

/-- Old rows are unchanged, up to the unavoidable dependent source-cut
transport. -/
theorem appendRow_row_old
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1)
    (i : Fin x.height) :
    HEq ((appendRow H x g).row i.castSucc) (x.row i) := by
  simp only [appendRow]
  have hi : i.1 < x.height := i.2
  exact FatTree.castRow_heq H _ (x.row i)

/-- The last row of an appended tree is the row that was appended. -/
theorem appendRow_row_last
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    HEq ((appendRow H x g).row (Fin.last x.height)) g := by
  simp only [appendRow]
  exact FatTree.castRow_heq H _ g

/-- Appending a row literally preserves the original finite prefix. -/
theorem appendRow_initialSegment
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    (appendRow H x g).initialSegment H x.height (by omega) = x := by
  refine FiniteFatTree.ext_pointwise H
    (U := (appendRow H x g).initialSegment H x.height (by omega))
    (V := x) rfl ?_ ?_
  · intro i
    change (appendRow H x g).cut i.1 = x.cut i
    let ii : Fin (x.height + 1) := ⟨i.1, i.2⟩
    have hc := appendRow_cut_old H x g ii
    simpa [ii] using hc
  · intro i
    change HEq ((appendRow H x g).row i.1) (x.row i)
    let ii : Fin x.height := ⟨i.1, i.2⟩
    have hr := appendRow_row_old H x g ii
    simpa [ii] using hr

end FiniteFatTree

end SMTree
end SuccessorTree
