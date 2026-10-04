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
  simp only [OneBlockLarge, not_forall] at hnot
  rcases hnot with ⟨V, hV⟩
  by_cases hVU : FatTree.Reduces H V U
  · by_cases hxV : ExtendsStem H x V
    · refine ⟨V, hVU, hxV, ?_⟩
      intro g hgV hgO
      have hex :
          ∃ g' : AM H x.terminalCut 1,
            g' ∈ O ∧ OneBlockOccurs H x V g' :=
        ⟨g, hgO, hgV⟩
      exact hV hVU hxV hex
    · exact False.elim (hV hVU hxV)
  · exact False.elim (hV hVU)

end FatTree

end SMTree
end SuccessorTree
