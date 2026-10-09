import SuccessorTree.V10.CanonicalBinary
import Mathlib.Tactic

/-!
# Canonical empty-or-singleton crossing parameters from E free levels

In Definition 6.30, the predecessor of a partial type at level
ell+1 is the restriction through ell, while its new ordinary
vertex ell has an E free level f. The parameter list is empty
exactly when f=0; otherwise its only parameter is the
partial type of ell over its own E free socle.

This module extracts that parameter from any concrete enumerated
partial structure and proves the strict source-level bound
f<ell for positive f, using E spacing and downward closure
rather than postulating the inequality.

This is a necessary local part of the actual successor
decomposition. The forward S construction, equality with
the manuscript's no-new-tuples operation, S2 uniqueness
and S3 existence on the forbidden-free Kpt tree still require
their own proofs.
-/

namespace SuccessorTree.V10

/-- A positive free E-cut is always strictly below the vertex
it belongs to; the spacing axiom rules out the border case. -/
theorem freeLevel_pos_lt_vertex
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hPos : 0 < A.freeLevel v) :
    A.freeLevel v < v := by
  let u := A.freeLevel v - 1
  have hu : u < A.freeLevel v := by omega
  have he : A.E u v = true :=
    (A.E_iff_freeLevel u v).2 hu
  have hgap := A.spaced u v he
  omega

/-- The actual parameter determined by the newly introduced
ordinary vertex. Its target type is a raw type at its unique
free cut, rather than a chosen arbitrary root-level type. -/
noncomputable def EnumeratedPartialStructure.insertionParameter
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) : Option (RawPartialTypeNode db du dd) :=
  if A.freeLevel v = 0 then none else some (A.rawTypeAtFree v)

/-- A crossing has no parameter exactly at free E-level zero. -/
theorem EnumeratedPartialStructure.insertionParameter_none_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) :
    A.insertionParameter v = none ↔ A.freeLevel v = 0 := by
  unfold EnumeratedPartialStructure.insertionParameter
  by_cases h : A.freeLevel v = 0 <;> simp [h]

/-- A nonempty parameter is uniquely the actual extracted
partial type of the new ordinary vertex, with positive free cut. -/
theorem EnumeratedPartialStructure.insertionParameter_some_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (p : RawPartialTypeNode db du dd) :
    A.insertionParameter v = some p ↔
      0 < A.freeLevel v ∧ p = A.rawTypeAtFree v := by
  unfold EnumeratedPartialStructure.insertionParameter
  by_cases h : A.freeLevel v = 0
  · simp [h]
  · have hp : 0 < A.freeLevel v := by omega
    simp [h, hp, eq_comm]

/-- The parameter of a nonempty crossing has level strictly below
its new ordinary vertex, as required by S1. -/
theorem EnumeratedPartialStructure.insertionParameter_level_lt
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (p : RawPartialTypeNode db du dd)
    (hp : A.insertionParameter v = some p) :
    p.1 < v := by
  obtain ⟨hpos, hpEq⟩ :=
    (A.insertionParameter_some_iff v p).1 hp
  subst p
  change A.freeLevel v < v
  exact freeLevel_pos_lt_vertex A v hpos

/-- A canonical nonempty parameter of a vertex in a forbidden-free
partial structure is itself an admissible partial type.
No global age or successor axioms are needed. -/
theorem EnumeratedPartialStructure.insertionParameter_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (p : RawPartialTypeNode db du dd)
    (hp : A.insertionParameter v = some p) :
    IsAdmissibleRawType family p := by
  obtain ⟨_, hpEq⟩ :=
    (A.insertionParameter_some_iff v p).1 hp
  subst p
  exact ⟨A, v, hv, hAvoid, rfl⟩

end SuccessorTree.V10
