import SuccessorTree.Block.ParityFatObstruction

/-!
# Independent extendibility is too strong for arbitrary marks

The unrestricted parity monoid permits the two canonical variable
blocks x11 and x. A marked cut through the constants between them
yields marked blocks x1 and 1x. Neither is independently an allowed
parity variable block, although concatenating the two marked blocks
is the same globally allowed ordered word x11x.

These elementary syntactic identities certify a genuine boundary
issue with the proposed GappedFatTree(H) structure whose every
width-two row must itself extend to the monoid. The English
interpretation to a full infinite M_odd member uses identity blocks
thereafter; it is not a typed weak monoid instance in this module.
-/

namespace SuccessorTree.Block
namespace ParityFat

def canonicalParityFirst : List (Option Bool) :=
  [none, some true, some true]

def canonicalParityNext : List (Option Bool) :=
  [none]

def splitMarkedFirst : List (Option Bool) :=
  [none, some true]

def splitMarkedNext : List (Option Bool) :=
  [some true, none]

theorem globally_admissible_x11 : AllowedParity canonicalParityFirst := by
  simp [canonicalParityFirst, AllowedParity, varCount, evaluate, weight]

theorem globally_admissible_x : AllowedParity canonicalParityNext := by
  simp [canonicalParityNext, AllowedParity, varCount, evaluate, weight]

theorem split_preserves_global_word :
    splitMarkedFirst ++ splitMarkedNext =
      canonicalParityFirst ++ canonicalParityNext := by
  rfl

theorem split_first_not_admissible :
    ¬ AllowedParity splitMarkedFirst := by
  simp [splitMarkedFirst, AllowedParity, varCount, evaluate, weight]

theorem split_next_not_admissible :
    ¬ AllowedParity splitMarkedNext := by
  simp [splitMarkedNext, AllowedParity, varCount, evaluate, weight]

end ParityFat
end SuccessorTree.Block
