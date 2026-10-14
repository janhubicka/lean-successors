import SuccessorTree.V10.ConcreteKptM1
import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# The E spacing obstruction and repair in Lemma 6.34

Delete an ordinary vertex at coordinate m from a finite enumerated
partial structure. The new ordinal has its m-th vertex at the
old coordinate m+1; every later vertex shifts down one.

Induced ordered L-tuples and E-tuples are copied exactly using the
strictly increasing deletion address map. Downward E-closure is
automatic. E spacing is NOT automatic: an original pair
(m-1,m+1) would become the forbidden consecutive pair
(m-1,m) after deletion.

The manuscript's hypothesis fl_A(m+1)<m rules out this pair,
because E(u,m+1) holds exactly when u<fl_A(m+1).
This module proves E spacing, downward closure and finite-domain
bounds under that sharp guard. No nontrivial M2 factorization or
shape-preserving deletion map is claimed here.
-/

namespace SuccessorTree.V10

/-- Position in the old enumeration of vertex x in the
enumeration with coordinate m deleted. -/
def deleteAt (m x : Nat) : Nat :=
  if x < m then x else x + 1

@[simp] theorem deleteAt_below (m x : Nat) (hx : x < m) :
    deleteAt m x = x := by
  simp [deleteAt, hx]

@[simp] theorem deleteAt_at (m : Nat) :
    deleteAt m m = m + 1 := by
  simp [deleteAt]

@[simp] theorem deleteAt_above (m x : Nat) (hx : m ≤ x) :
    deleteAt m x = x + 1 := by
  have hnot : ¬ x < m := Nat.not_lt.mpr hx
  simp [deleteAt, hnot]

theorem deleteAt_strictMono (m : Nat) :
    StrictMono (deleteAt m) := by
  intro x y hxy
  by_cases hx : x < m
  · by_cases hy : y < m
    · simp [deleteAt, hx, hy]; exact hxy
    · have hyn : ¬ y < m := hy
      simp only [deleteAt, if_pos hx, if_neg hyn]
      omega
  · have hyn : ¬ y < m := by omega
    simp only [deleteAt, if_neg hx, if_neg hyn]
    omega

/-- Induced E relation after removing numbered vertex m. -/
def deleteAtE
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m u v : Nat) : Bool :=
  A.E (deleteAt m u) (deleteAt m v)

/-- The induced E relation remains downward closed automatically. -/
theorem deleteAtE_downward
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat) :
    DownwardE (deleteAtE A m) := by
  intro u v he z hz
  exact A.downward (deleteAt m u) (deleteAt m v) he
    (deleteAt m z) (deleteAt_strictMono m hz)

/-- The deletion boundary is the only possible violation of E spacing.
The *strict* free-cut guard at the immediately following old vertex
eliminates that obstruction. -/
theorem deleteAtE_spaced
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat)
    (hnext : m + 1 < A.size)
    (hfree : A.freeLevel (m + 1) < m) :
    SpacedE (deleteAtE A m) := by
  intro u v he
  have hOldSpace := A.spaced (deleteAt m u) (deleteAt m v) he
  by_cases hu : u < m
  · by_cases hv : v < m
    · simp only [deleteAt_below m u hu,
          deleteAt_below m v hv] at hOldSpace
      exact hOldSpace
    · have hv' : m ≤ v := by omega
      simp only [deleteAt_below m u hu,
          deleteAt_above m v hv'] at hOldSpace
      by_contra hGap
      have hEq : u + 1 = v := by omega
      have hvEq : v = m := by omega
      have hOldE : A.E u (m + 1) = true := by
        simpa [deleteAtE, deleteAt, hu, hvEq] using he
      have hLt := (A.E_iff_freeLevel u (m + 1)).mp hOldE
      omega
  · have hu' : m ≤ u := by omega
    by_cases hv : v < m
    · simp only [deleteAt_above m u hu',
          deleteAt_below m v hv] at hOldSpace
      omega
    · have hv' : m ≤ v := by omega
      simp only [deleteAt_above m u hu',
          deleteAt_above m v hv'] at hOldSpace
      omega

/-- Any induced E pair between remaining vertices stays inside
the shortened enumeration. -/
theorem deleteAtE_inside
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (m : Nat) (hnext : m + 1 < A.size)
    (u v : Nat) (he : deleteAtE A m u v = true) :
    u < A.size - 1 ∧ v < A.size - 1 := by
  have hOld := A.E_inside (deleteAt m u) (deleteAt m v) he
  have hu : u < A.size - 1 := by
    by_cases hm : u < m
    · have heq := deleteAt_below m u hm
      rw [heq] at hOld
      omega
    · have heq := deleteAt_above m u (by omega)
      rw [heq] at hOld
      omega
  have hv : v < A.size - 1 := by
    by_cases hm : v < m
    · have heq := deleteAt_below m v hm
      rw [heq] at hOld
      omega
    · have heq := deleteAt_above m v (by omega)
      rw [heq] at hOld
      omega
  exact ⟨hu,hv⟩


/-- A sharp counterexample to replacing the strict deletion guard by
a weak inequality. Its only nonempty E column is the initial segment
u<m at the old vertex m+1, so its free level there equals m. -/
def deletionBoundaryE (m u v : Nat) : Bool :=
  decide (v = m + 1 ∧ u < m)

/-- This boundary E relation is a genuine spaced relation. -/
theorem deletionBoundaryE_spaced (m : Nat) :
    SpacedE (deletionBoundaryE m) := by
  intro u v he
  have hh : v = m + 1 ∧ u < m := by
    simpa [deletionBoundaryE] using he
  omega

/-- Its columns are downward closed. -/
theorem deletionBoundaryE_downward (m : Nat) :
    DownwardE (deletionBoundaryE m) := by
  intro u v he w hw
  have hh : v = m + 1 ∧ u < m := by
    simpa [deletionBoundaryE] using he
  rcases hh with ⟨hv, hu⟩
  simp [deletionBoundaryE, hv, lt_trans hw hu]

/-- Exactly the borderline weak bound fl(m+1)=m holds. -/
theorem deletionBoundaryE_freeCut (m : Nat) :
    IsFreeCut (deletionBoundaryE m) (m + 1) m := by
  constructor
  · intro u hu
    simp [deletionBoundaryE, hu]
  · simp [deletionBoundaryE]

/-- Deleting m from this valid spaced/downward E relation produces
the illegal consecutive E pair (m-1,m). Thus
fl(m+1)≤m is insufficient; the manuscript's strict
fl(m+1)<m guard is sharp. -/
theorem deletionBoundaryE_weak_guard_fails
    (m : Nat) (hm : 0 < m) :
    ¬ SpacedE
      (fun u v => deletionBoundaryE m (deleteAt m u) (deleteAt m v)) := by
  intro hSpace
  let u := m - 1
  have hu : u < m := by
    dsimp [u]
    omega
  have hE : deletionBoundaryE m (deleteAt m u)
      (deleteAt m m) = true := by
    rw [deleteAt_below m u hu, deleteAt_at m]
    exact show deletionBoundaryE m u (m + 1) = true by
      simp [deletionBoundaryE, hu]
  have hBad := hSpace u m hE
  dsimp [u] at hBad
  omega

end SuccessorTree.V10
