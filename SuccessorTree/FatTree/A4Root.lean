import SuccessorTree.ShapeSplit
import SuccessorTree.ShapeTransportAlphabet

/-!
# The root-level dichotomy for fat-tree A4

M3 supplies immediate successors at every positive level. At level zero,
a moving row yields a genuine one-level letter by truncation and canonical
extension. Such a letter supplies successors of every root. Otherwise every
root row is the identity. No global pruning assumption is introduced.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable (H : SMTree S)

/-- A moving root row produces a genuine letter skipping zero. -/
theorem exists_rootLetter_of_topLevel_pos
    (g : AM H 0 1) (hg : 0 < g.topLevel H) :
    Nonempty (OneLevelLetter H 0) := by
  obtain ⟨G, hfix, htop, _⟩ :=
    exists_truncate_moving_level H (g.representative H) 0 1
      (g.representative_fixesBelow H) (by omega)
      (by change 1 ≤ g.topLevel H; omega)
  exact ⟨⟨H.canonicalExtension G 0,
    H.canonicalExtension_skipsOnly_of_oneStep G 0 hfix htop⟩⟩

/-- Without a root letter, the root-row type is a singleton. -/
theorem rootRow_eq_id1_of_no_rootLetter
    (hno : ¬ Nonempty (OneLevelLetter H 0))
    (g : AM H 0 1) :
    g = AM.id1 H 0 := by
  apply AM.eq_id1_of_topLevel_le H
  by_contra htop
  have hpos : 0 < g.topLevel H := by omega
  exact hno (H.exists_rootLetter_of_topLevel_pos g hpos)

/-- Equivalently, a nontrivial root row forces a root letter. -/
theorem nontrivial_rootRow_implies_rootLetter
    (g : AM H 0 1) (hne : g ≠ AM.id1 H 0) :
    Nonempty (OneLevelLetter H 0) := by
  by_contra hno
  exact hne (H.rootRow_eq_id1_of_no_rootLetter hno g)

/-- A root letter, together with M3 at positive levels, prunes the whole tree. -/
theorem exists_immediateSuccessor_of_rootLetter
    (hroot : Nonempty (OneLevelLetter H 0)) (x : T) :
    ∃ y : T, x ⋖ y := by
  by_cases hx : LevelTree.lev x = 0
  · rcases hroot with ⟨E⟩
    exact ⟨E x, H.letter_covBy E hx⟩
  · exact H.exists_immediateSuccessor_of_level_pos x (Nat.pos_of_ne_zero hx)

end SMTree
end SuccessorTree
