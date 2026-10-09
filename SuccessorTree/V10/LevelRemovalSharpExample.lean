import SuccessorTree.V10.LevelRemovalFreeCut
import Mathlib.Tactic

/-!
# The strict deletion guard cannot be weakened, even for genuine partial structures

The exact E counterexample in LevelRemovalE already shows that
fl_A(m+1)=m makes the induced deletion E relation violate spacing.

Here we realize that counterexample as a complete enumerated L+ partial
structure in ANY finite unary/binary signature. All L atoms are false.
Thus E3 is vacuous, and the E relation obeys spacing and downward
closure. Its free level at the next vertex m+1 equals m.

Deleting m then produces the illegal consecutive E pair (m-1,m).
This proves at the level of GENUINE partial structures (not just an
abstract relation) that the weaker fl_A(m+1)≤m guard does not suffice.

The result should be mentioned as a short adversarial validation
note next to the strict inequality in Lemma 6.34.
-/

namespace SuccessorTree.V10

/-- A genuine enumerated finite partial structure whose only
nonempty E column is the full initial segment at vertex m+1.
Its L reduct is empty in every relation. -/
def deletionBoundaryPartial
    (db du dd m : Nat) :
    EnumeratedPartialStructure db du dd := by
  refine
    { size := m + 2
      L :=
        { carrier := {x | x < m + 2}
          binary := fun _ _ _ => false
          unary := fun _ _ => false
          diagonal := fun _ _ => false }
      carrier_iff := ?_
      E := deletionBoundaryE m
      E_inside := ?_
      spaced := deletionBoundaryE_spaced m
      downward := deletionBoundaryE_downward m
      linked_E := ?_ }
  · intro v
    rfl
  · intro u v he
    have h : v = m + 1 ∧ u < m := by
      simpa [deletionBoundaryE] using he
    constructor <;> omega
  · intro u v huv hu hv hlink
    change (∃ r : Fin db, false = true ∨ false = true) at hlink
    simp at hlink

/-- The unique free level of the next vertex is EXACTLY m. -/
theorem deletionBoundaryPartial_freeLevel
    (db du dd m : Nat) :
    (deletionBoundaryPartial db du dd m).freeLevel (m + 1) = m := by
  let A := deletionBoundaryPartial db du dd m
  have hCut : IsFreeCut A.E (m + 1) m :=
    deletionBoundaryE_freeCut m
  exact freeCut_unique A.E (m + 1) (A.freeLevel (m + 1)) m
    (canonicalFreeLevel_isFreeCut A.E A.spaced A.downward (m + 1))
    hCut

/-- In every finite unary/binary language, there exists a genuine
partial structure satisfying the WEAK free-cut condition
fl_A(m+1)≤m, but deletion of m breaks the E spacing axiom.
This certifies why the STRICT guard in Lemma 6.34 is sharp. -/
theorem weak_level_removal_guard_counterexample
    (db du dd m : Nat) (hm : 0 < m) :
    ∃ A : EnumeratedPartialStructure db du dd,
      m + 1 < A.size ∧
      A.freeLevel (m + 1) ≤ m ∧
      ¬ SpacedE (deleteAtE A m) := by
  let A := deletionBoundaryPartial db du dd m
  refine ⟨A, ?_, ?_, ?_⟩
  · change m + 1 < m + 2
    omega
  · have h := deletionBoundaryPartial_freeLevel db du dd m
    change A.freeLevel (m + 1) = m at h
    omega
  · change ¬ SpacedE
      (fun u v => deletionBoundaryE m (deleteAt m u) (deleteAt m v))
    exact deletionBoundaryE_weak_guard_fails m hm

end SuccessorTree.V10
