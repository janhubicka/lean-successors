import SuccessorTree.FatTree.A4Trace
import SuccessorTree.FatTree.Amalgamation

/-!
# Large one-block sets for fat-tree A4

The manuscript fixes a finite stem and asks whether every refinement preserving
that stem contains a legal next block from a given set.  Keeping the stem as
an explicit argument avoids dependent casts when the ambient infinite fat tree
is refined.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

namespace FatTree

variable (H : SMTree S)

/-- A row is a legal one-block extension of a finite stem inside an infinite
fat tree when the appended finite fat tree occurs at some finite depth. -/
def OneBlockOccurs
    (x : FiniteFatTree H) (U : FatTree H)
    (g : AM H x.terminalCut 1) : Prop :=
  ∃ m : Nat, StemAt H (FiniteFatTree.appendRow H x g) U m

/-- The ambient row immediately after a literal finite stem, transported
to the stem's terminal-cut type. -/
noncomputable def ambientNextRow
    (x : FiniteFatTree H) (U : FatTree H)
    (hxU : ExtendsStem H x U) :
    AM H x.terminalCut 1 :=
  FatTree.castRow H
    (terminalCut_eq_of_extendsStem H hxU)
    (U.row x.height)

/-- Appending the ambient next row to a literal stem gives exactly the next
finite initial segment of the ambient fat tree. -/
theorem appendRow_ambientNextRow
    (x : FiniteFatTree H) (U : FatTree H)
    (hxU : ExtendsStem H x U) :
    FiniteFatTree.appendRow H x (ambientNextRow H x U hxU) =
      U.initialSegment H (x.height + 1) := by
  let g : AM H x.terminalCut 1 := ambientNextRow H x U hxU
  refine FiniteFatTree.ext_pointwise H rfl ?_ ?_
  · intro i
    by_cases hi : i.1 ≤ x.height
    · by_cases hlast : i.1 = x.height + 1
      · omega
      · have hiOld : i.1 ≤ x.height := hi
        let ix : Fin (x.height + 1) :=
          ⟨i.1, Nat.lt_succ_of_le hiOld⟩
        have hiCast :
            Fin.cast
              (congrArg (fun n => n + 1) rfl)
              i = i := by rfl
        have hcutx :=
          cut_eq_of_extendsStem H hxU ix
        calc
          (FiniteFatTree.appendRow H x g).cut i =
              x.cut ix := by
                have h :=
                  FiniteFatTree.appendRow_cut_old H x g ix
                simpa [ix] using h
          _ = U.cut ix.1 := hcutx.symm
          _ = (U.initialSegment H (x.height + 1)).cut i := by
                rfl
    · have hieq : i.1 = x.height + 1 := by omega
      have hiLast :
          i = Fin.last (x.height + 1) := by
        apply Fin.ext
        exact hieq
      rw [hiLast]
      rw [FiniteFatTree.appendRow_terminalCut]
      change g.rowEndLevel H + 1 = U.cut (x.height + 1)
      have hgEnd :
          g.rowEndLevel H = (U.row x.height).rowEndLevel H := by
        simp [g, ambientNextRow]
      rw [hgEnd]
      exact U.row_cut x.height
  · intro i
    by_cases hi : i.1 < x.height
    · let ix : Fin x.height := ⟨i.1, hi⟩
      have hxrow :=
        FiniteFatTree.row_heq_of_eq (H := H) hxU.symm ix
      have happ :=
        FiniteFatTree.appendRow_row_old H x g ix
      have hiEq :
          i = ix.castSucc := by
        apply Fin.ext
        rfl
      rw [hiEq]
      exact HEq.trans happ hxrow.symm
    · have hieq : i.1 = x.height := by omega
      have hiLast : i = Fin.last x.height := by
        apply Fin.ext
        exact hieq
      rw [hiLast]
      have happ :=
        FiniteFatTree.appendRow_row_last H x g
      have hg :
          HEq g (U.row x.height) := by
        unfold g ambientNextRow
        exact FatTree.castRow_heq H
          (terminalCut_eq_of_extendsStem H hxU)
          (U.row x.height)
      exact HEq.trans happ hg

/-- The ambient next row always occurs at the next depth. -/
theorem ambientNextRow_occurs
    (x : FiniteFatTree H) (U : FatTree H)
    (hxU : ExtendsStem H x U) :
    OneBlockOccurs H x U (ambientNextRow H x U hxU) := by
  refine ⟨x.height + 1, ?_⟩
  unfold StemAt
  rw [appendRow_ambientNextRow H x U hxU]
  exact FiniteFatTree.leFin_refl H (U.initialSegment H (x.height + 1))

/-- A set of possible next rows is large below an ambient fat tree with a
fixed literal stem if every reduction preserving that stem contains a legal
row from the set.

This is the stem-based form of the manuscript's `(U,n)`-largeness. -/
def OneBlockLarge
    (x : FiniteFatTree H) (U : FatTree H)
    (O : Set (AM H x.terminalCut 1)) : Prop :=
  ∀ V : FatTree H,
    FatTree.Reduces H V U →
    ExtendsStem H x V →
    ∃ g : AM H x.terminalCut 1,
      g ∈ O ∧ OneBlockOccurs H x V g

/-- Largeness is monotone under refinements that preserve the fixed stem. -/
theorem oneBlockLarge_mono
    {x : FiniteFatTree H} {U V : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hlarge : OneBlockLarge H x U O)
    (hVU : FatTree.Reduces H V U)
    (hxV : ExtendsStem H x V) :
    OneBlockLarge H x V O := by
  intro W hWV hxW
  exact hlarge W
    (FatTree.reduces_trans H hWV hVU)
    hxW

/-- Enlarging the set of accepted next rows preserves largeness. -/
theorem oneBlockLarge_superset
    {x : FiniteFatTree H} {U : FatTree H}
    {O O' : Set (AM H x.terminalCut 1)}
    (hlarge : OneBlockLarge H x U O)
    (hOO' : O ⊆ O') :
    OneBlockLarge H x U O' := by
  intro V hVU hxV
  rcases hlarge V hVU hxV with ⟨g, hgO, hgV⟩
  exact ⟨g, hOO' hgO, hgV⟩

/-- If a set is not large, there is a refinement preserving the stem which
avoids every legal next block from that set. -/
theorem exists_avoiding_refinement_of_not_large
    {x : FiniteFatTree H} {U : FatTree H}
    {O : Set (AM H x.terminalCut 1)}
    (hnot : ¬ OneBlockLarge H x U O) :
    ∃ V : FatTree H,
      FatTree.Reduces H V U ∧
      ExtendsStem H x V ∧
      ∀ g : AM H x.terminalCut 1,
        OneBlockOccurs H x V g → g ∉ O := by
  classical
  simp only [OneBlockLarge, not_forall, not_exists, not_and] at hnot
  rcases hnot with ⟨V, hVU, hxV, havoid⟩
  refine ⟨V, hVU, hxV, ?_⟩
  intro g hgV hgO
  exact havoid g hgO hgV

/-- Binary partition step for large one-block sets.  After a
stem-preserving refinement, one of the two cells remains large. -/
theorem oneBlockLarge_partition
    {x : FiniteFatTree H} {U : FatTree H}
    {O O₀ O₁ : Set (AM H x.terminalCut 1)}
    (hxU : ExtendsStem H x U)
    (hlarge : OneBlockLarge H x U O)
    (hpart : O ⊆ O₀ ∪ O₁) :
    ∃ V : FatTree H,
      FatTree.Reduces H V U ∧
      ExtendsStem H x V ∧
      (OneBlockLarge H x V O₀ ∨
       OneBlockLarge H x V O₁) := by
  classical
  by_cases h₀ : OneBlockLarge H x U O₀
  · exact ⟨U, FatTree.reduces_refl H U, hxU, Or.inl h₀⟩
  · rcases exists_avoiding_refinement_of_not_large H h₀ with
      ⟨V, hVU, hxV, havoid⟩
    refine ⟨V, hVU, hxV, Or.inr ?_⟩
    intro W hWV hxW
    have hWU : FatTree.Reduces H W U :=
      FatTree.reduces_trans H hWV hVU
    rcases hlarge W hWU hxW with ⟨g, hgO, hgW⟩
    have hgV : OneBlockOccurs H x V g := by
      rcases hgW with ⟨k, hgk⟩
      rcases exists_stemAt_of_reduces H hgk hWV with
        ⟨m, hgm⟩
      exact ⟨m, hgm⟩
    have hgNot0 : g ∉ O₀ := havoid g hgV
    have hgUnion : g ∈ O₀ ∪ O₁ := hpart hgO
    have hg1 : g ∈ O₁ := by
      rcases hgUnion with hg0 | hg1
      · exact False.elim (hgNot0 hg0)
      · exact hg1
    exact ⟨g, hg1, hgW⟩

end FatTree

end SMTree
end SuccessorTree
