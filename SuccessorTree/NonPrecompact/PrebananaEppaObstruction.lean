import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Atom-count obstruction to pre-BANANA EPPA

The circulation manuscript uses one elementary finite invariant.  An
automorphism of a finite Boolean algebra permutes its ambient atoms, hence
preserves the number of atoms below each element.  Consequently it cannot
send an element to a strict enlargement by a disjoint nonempty element.

This file isolates that counting obstruction independently of the Boolean
algebra presentation.  It is the exact finite combinatorial step in the
pre-BANANA non-EPPA argument.
-/

namespace SuccessorTree.NonPrecompact

/-- A permutation of a finite ambient atom set cannot send a block to its
union with a disjoint nonempty block. -/
theorem no_perm_maps_finset_to_disjoint_union
    {α : Type*} [Fintype α] [DecidableEq α]
    (a b : Finset α)
    (hdisj : Disjoint a b)
    (hb : b.Nonempty) :
    ¬ ∃ e : Equiv.Perm α, a.image e = a ∪ b := by
  rintro ⟨e, he⟩
  have himage :
      (a.image e).card = a.card :=
    Finset.card_image_of_injective a e.injective
  have hunion :
      (a ∪ b).card = a.card + b.card :=
    Finset.card_union_of_disjoint hdisj
  rw [he, hunion] at himage
  have hbpos : 0 < b.card :=
    Finset.card_pos.mpr hb
  omega

/-- Equivalent strict-cardinality formulation used when the source element
is represented by a subset of ambient atoms and the target contains at least
one additional disjoint atom. -/
theorem card_lt_disjoint_union
    {α : Type*} [DecidableEq α]
    (a b : Finset α)
    (hdisj : Disjoint a b)
    (hb : b.Nonempty) :
    a.card < (a ∪ b).card := by
  rw [Finset.card_union_of_disjoint hdisj]
  exact Nat.lt_add_of_pos_right (Finset.card_pos.mpr hb)

end SuccessorTree.NonPrecompact
