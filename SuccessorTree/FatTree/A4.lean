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
private noncomputable def appendCut
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
        rw [hieq]
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
  have hc :
      x.cut i.castSucc = appendCut H x g i.1 := by
    have h :=
      appendCut_old H x g (i := i.1) (Nat.le_of_lt i.2)
    have hi :
        (⟨i.1, by omega⟩ : Fin (x.height + 1)) =
          i.castSucc := Fin.ext rfl
    rw [h, hi]
  have hcast := FatTree.castRow_heq H hc (x.row i)
  simpa [appendRow, i.2] using hcast

/-- The last row of an appended tree is the row that was appended. -/
theorem appendRow_row_last
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    HEq ((appendRow H x g).row (Fin.last x.height)) g := by
  have hc :
      x.terminalCut = appendCut H x g x.height := by
    have h := appendCut_old H x g (i := x.height) le_rfl
    rw [h]
    rfl
  have hcast := FatTree.castRow_heq H hc g
  simpa [appendRow] using hcast

/-- The canonical extension of the appended last row is literally the
canonical extension of the row that was appended. -/
theorem appendRow_rowExtension_last
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    (appendRow H x g).rowExtension H (Fin.last x.height) =
      H.canonicalExtension (g.representative H) x.terminalCut := by
  have hcut :
      (appendRow H x g).cut (Fin.last x.height).castSucc =
        x.terminalCut := by
    simpa [FiniteFatTree.terminalCut] using
      appendRow_cut_old H x g (Fin.last x.height)
  have hrow :
      HEq ((appendRow H x g).row (Fin.last x.height)) g :=
    appendRow_row_last H x g
  unfold FiniteFatTree.rowExtension
  exact FatTree.canonicalExtension_eq_of_row_heq H hcut hrow

/-- The last one-step Lift after appending g is therefore the image of
the successor fan under the canonical extension g-plus. -/
theorem appendRow_oneLift_last
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1)
    (X : Set T) :
    (appendRow H x g).oneLift H (Fin.last x.height) X =
      H.canonicalExtension (g.representative H) x.terminalCut ''
        ImmediateSuccessors (T := T) X := by
  unfold FiniteFatTree.oneLift
  rw [appendRow_rowExtension_last H x g]

/-- Appending a row literally preserves the original finite prefix. -/
theorem appendRow_initialSegment
    (x : FiniteFatTree H)
    (g : AM H x.terminalCut 1) :
    (appendRow H x g).initialSegment H x.height
      (by rw [appendRow_height]; omega) = x := by
  let hxle : x.height ≤ (appendRow H x g).height := by
    rw [appendRow_height]
    omega
  refine FiniteFatTree.ext_pointwise H
    (U := (appendRow H x g).initialSegment H x.height hxle)
    (V := x) rfl ?_ ?_
  · intro i
    let ii : Fin (x.height + 1) :=
      ⟨i.1, by simpa using i.2⟩
    have hseg :
        ((appendRow H x g).initialSegment H x.height hxle).cut i =
          (appendRow H x g).cut ii.castSucc := by
      rfl
    calc
      ((appendRow H x g).initialSegment H x.height hxle).cut i =
          (appendRow H x g).cut ii.castSucc := hseg
      _ = x.cut ii := appendRow_cut_old H x g ii
      _ = x.cut i := by
        congr 1
  · intro i
    let ii : Fin x.height := ⟨i.1, by simpa using i.2⟩
    have hseg :
        HEq
          (((appendRow H x g).initialSegment H x.height hxle).row i)
          ((appendRow H x g).row ii.castSucc) := by
      rfl
    exact hseg.trans (appendRow_row_old H x g ii)

end FiniteFatTree

end SMTree
end SuccessorTree
