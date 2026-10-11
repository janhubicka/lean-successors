import SuccessorTree.V10.LevelRemovalPrefixCommute
import SuccessorTree.V10.RawPrefixOrder
import Mathlib.Tactic

/-!
# Coordinate deletion preserves the complete raw Kpt prefix order

The level-removal map in the paper deletes the same ordinary coordinate
m from every image type at or above the chosen source level. The local
mathematical order statement is stronger than deleting merely its
L-reduct: if two complete L+ types are in the actual prefix relation,
and both cuts lie above m, then the shortened complete types remain
in the actual prefix relation.

This theorem is independent of age and uses NO M2, ShapeMap or
additional completion assumption. Admissibility of the shortened
types, injectivity and the weak successor condition for the eventual
global map are separate obligations.
-/

namespace SuccessorTree.V10

/-- The candidate raw type obtained by deleting an ordinary socle
coordinate m. This is an actual complete L+ record, but it is NOT
declared admissible without a separate forbidden-free witness. -/
def rawPartialTypeDeleteAt
    {db du dd : Nat}
    (N : RawPartialTypeNode db du dd)
    (m : Nat) (hm : m < N.1) : RawPartialTypeNode db du dd :=
  ⟨N.1 - 1, N.2.deleteOrdinary m hm⟩

/-- The candidate's level is exactly one smaller than the original
level. No canonical new free-cut identification is hidden here. -/
@[simp] theorem rawPartialTypeDeleteAt_level
    {db du dd : Nat}
    (N : RawPartialTypeNode db du dd)
    (m : Nat) (hm : m < N.1) :
    (rawPartialTypeDeleteAt N m hm).1 = N.1 - 1 := rfl

/-- Literal complete-prefix preservation under deletion of the
same ordinary coordinate from both inputs. Every old L and E atom
is treated simultaneously by the checked deletion/restriction
commutation theorem. -/
theorem rawPartialTypeDeleteAt_prefix
    {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd}
    (hab : a ≤ b) (m : Nat) (hm : m < a.1) :
    rawPartialTypeDeleteAt a m hm ≤
      rawPartialTypeDeleteAt b m
        (lt_of_lt_of_le hm hab.1) := by
  let hmb : m < b.1 := lt_of_lt_of_le hm hab.1
  have hRecord : a.2 = b.2.restrict hab.1 := hab.2
  change a.1 - 1 ≤ b.1 - 1 ∧
    a.2.deleteOrdinary m hm =
      (b.2.deleteOrdinary m hmb).restrict
        (Nat.sub_le_sub_right hab.1 1)
  constructor
  · exact Nat.sub_le_sub_right hab.1 1
  · calc
      a.2.deleteOrdinary m hm =
          (b.2.restrict hab.1).deleteOrdinary m hm :=
        congrArg
          (fun Q : PartialTypeWithE a.1 db du dd =>
            Q.deleteOrdinary m hm) hRecord
      _ = (b.2.deleteOrdinary m hmb).restrict
          (Nat.sub_le_sub_right hab.1 1) :=
        (PartialTypeWithE.deleteOrdinary_restrict b.2 hab.1 m hm).symm

end SuccessorTree.V10
