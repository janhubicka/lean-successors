import SuccessorTree.V10.LevelRemovalE
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Delete a numbered vertex while retaining a forbidden-free partial structure

This is the finite structure-level ingredient of the manuscript's
level-removal lemma 6.34. Remove coordinate m from an enumerated
partial structure A, renumber subsequent vertices downward,
and copy every remaining positive AND negative L and E atom.

If the following old vertex m+1 has free cut strictly below m,
the new E relation has spacing and downward closure. The third
partial-structure axiom E3 passes to the induced substructure.
The L-reduct preserves the complete ordered induced age of A,
so no forbidden structure can appear after deletion.

The construction is local. To establish Lemma 6.34 itself one must
still define deletion *uniformly on all Kpt types at and above a
target source level*, preserve the distinguished type vertex t,
and prove weak successor preservation for the resulting map.
-/

namespace SuccessorTree.V10

/-- Literal induced L-reduct on the ordinal with vertex m deleted. -/
def deleteAtL
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat) : AgeTestModel db du dd :=
  { carrier := {x | x < A.size - 1}
    binary := fun x y r =>
      A.L.binary (deleteAt m x) (deleteAt m y) r
    unary := fun x r =>
      A.L.unary (deleteAt m x) r
    diagonal := fun x r =>
      A.L.diagonal (deleteAt m x) r }

/-- The whole induced L+ reduct after deleting m is again a
partial structure when the sharp E spacing guard is satisfied. -/
def deleteAtPartial
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hfree : A.freeLevel (m + 1) < m) :
    EnumeratedPartialStructure db du dd := by
  refine
    { size := A.size - 1
      L := deleteAtL A m
      carrier_iff := ?_
      E := deleteAtE A m
      E_inside := deleteAtE_inside A m hnext
      spaced := deleteAtE_spaced A m hnext hfree
      downward := deleteAtE_downward A m
      linked_E := ?_ }
  · intro v
    rfl
  · intro u v huv hu hv hlink
    have hOldU : deleteAt m u < A.size := by
      by_cases hm : u < m
      · rw [deleteAt_below m u hm]
        omega
      · rw [deleteAt_above m u (by omega)]
        omega
    have hOldV : deleteAt m v < A.size := by
      by_cases hm : v < m
      · rw [deleteAt_below m v hm]
        omega
      · rw [deleteAt_above m v (by omega)]
        omega
    have hOldRel :
        ∃ r : Fin db,
          A.L.binary (deleteAt m u) (deleteAt m v) r = true ∨
          A.L.binary (deleteAt m v) (deleteAt m u) r = true := by
      exact hlink
    exact A.linked_E (deleteAt m u) (deleteAt m v)
      (deleteAt_strictMono m huv) hOldU hOldV hOldRel

/-- The original L-reduct on a subset is recovered exactly as the
induced structure after the coordinate deletion. -/
theorem deleteAtL_realizes_implies_original
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat) (hnext : m + 1 < A.size)
    (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat)
    (hCopy : (deleteAtL A m).Realizes F f) :
    A.L.Realizes F (fun i => deleteAt m (f i)) := by
  obtain ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩ := hCopy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact deleteAt_strictMono m (hMono hab)
  · intro a
    apply (A.carrier_iff (deleteAt m (f a))).2
    have hf : f a < A.size - 1 := hIn a
    by_cases hm : f a < m
    · rw [deleteAt_below m (f a) hm]
      omega
    · rw [deleteAt_above m (f a) (by omega)]
      omega
  · intro a b hab t
    exact hBinary a b hab t
  · intro a t
    exact hUnary a t
  · intro a t
    exact hDiagonal a t

/-- Induced coordinate deletion cannot create an ordered
forbidden L-copy; irreducibility is NOT needed for this direction. -/
theorem deleteAtL_preserves_avoidance
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat) (hnext : m + 1 < A.size)
    (F : ForbiddenAtomicPattern r db du dd)
    (hAvoid : ¬ ∃ f : Fin r → Nat, A.L.Realizes F f) :
    ¬ ∃ f : Fin r → Nat, (deleteAtL A m).Realizes F f := by
  rintro ⟨f, hCopy⟩
  exact hAvoid ⟨_, deleteAtL_realizes_implies_original
    A m hnext F f hCopy⟩

/-- All forbidden structures in the normalized family remain
avoided after literal induced coordinate deletion. -/
theorem NormalizedForbidden.deleteAt_preserves_avoidance
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat) (hnext : m + 1 < A.size)
    (hAvoid : bad.Avoids A.L) :
    bad.Avoids (deleteAtL A m) := by
  cases bad with
  | singleton F _ =>
      exact deleteAtL_preserves_avoidance A m hnext F hAvoid
  | nontrivial r F _ _ =>
      exact deleteAtL_preserves_avoidance A m hnext F hAvoid

/-- The result of a deletion satisfying the sharp free-cut guard is
an ordinary finite forbidden-free partial structure whenever A was.
This is not yet the global level-removal shape-map theorem. -/
theorem deleteAtPartial_preserves_avoidance
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hfree : A.freeLevel (m + 1) < m)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    ∀ bad, bad ∈ family →
      bad.Avoids (deleteAtPartial A m hnext hfree).L := by
  intro bad hMem
  exact bad.deleteAt_preserves_avoidance
    A m hnext (hAvoid bad hMem)

end SuccessorTree.V10
