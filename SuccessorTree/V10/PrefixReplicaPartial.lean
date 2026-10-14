import SuccessorTree.V10.PrefixReplicaL
import SuccessorTree.V10.PrefixReplicaE
import Mathlib.Tactic

/-!
# The one-neutral-filler replica really is a partial structure

Combine the exact copied L-reduct with the preserved E relation.
For a vertex v in a finite enumerated partial structure A and
a cut d <= fl_A(v), retain the first d vertices, insert one neutral
filler at d, and relocate v to d+1.

All THREE partial-structure axioms of Definition 6.28 follow:
the E relation has spacing and downward closure; any irreducible
ordered L pair is E-related. The relocated vertex has free level
exactly d, and its complete induced L+ partial type is precisely
the original type of v through d, including all E and L facts.

This proves the elementary geometric prefix-realization step,
but does NOT by itself prove the new L-reduct is F-free. That
requires the allowed neutral singleton and irreducibility of
every nontrivial forbidden structure.
-/

namespace SuccessorTree.V10

/-- Complete partial-structure replica, using the same E and L
constructions already verified independently. -/
noncomputable def prefixReplicaPartialStructure
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v d : Nat) (hv : v < A.size)
    (hd : d ≤ A.freeLevel v) :
    EnumeratedPartialStructure db du dd := by
  refine
    { size := d + 2
      L := prefixReplicaL A d v
      carrier_iff := ?_
      E := prefixReplicaE A d
      E_inside := ?_
      spaced := prefixReplicaE_spaced A d
      downward := prefixReplicaE_downward A d
      linked_E := ?_ }
  · intro x
    rfl
  · intro u w h
    by_cases hw : w < d
    · have hOld : A.E u w = true := by
        simpa [prefixReplicaE, hw] using h
      have hgap := A.spaced u w hOld
      constructor <;> omega
    · by_cases hLast : w = d + 1
      · have hu : u < d := by
          have h' : prefixReplicaE A d u (d + 1) = true := by
            simpa [hLast] using h
          exact (prefixReplicaE_last_iff A d u).1 h'
        constructor <;> omega
      · simp [prefixReplicaE, hw, hLast] at h
  · intro u w huw hu hw hlink
    by_cases hwOld : w < d
    · have huOld : u < d := by omega
      have hOldLinked :
          ∃ r : Fin db,
            A.L.binary u w r = true ∨
            A.L.binary w u r = true := by
        obtain ⟨r, hr⟩ := hlink
        refine ⟨r, ?_⟩
        rcases hr with hr | hr
        · left
          simpa [prefixReplicaL,
            prefixReplicaAddress_old d v u huOld,
            prefixReplicaAddress_old d v w hwOld] using hr
        · right
          simpa [prefixReplicaL,
            prefixReplicaAddress_old d v w hwOld,
            prefixReplicaAddress_old d v u huOld] using hr
      have hSizeV : d ≤ A.size :=
        (hd.trans (A.freeLevel_le v)).trans (Nat.le_of_lt hv)
      have hE : A.E u w = true :=
        A.linked_E u w huw
          (lt_of_lt_of_le huOld hSizeV)
          (lt_of_lt_of_le hwOld hSizeV)
          hOldLinked
      exact (prefixReplicaE_old A d u w hwOld).trans hE
    · have hPoss : w = d ∨ w = d + 1 := by omega
      rcases hPoss with hFill | hLast
      · subst w
        obtain ⟨r, hr⟩ := hlink
        have hNeutral := (prefixReplicaL_filler_neutral A d v u).1 r
        rcases hr with hr | hr
        · exact False.elim (by simpa [hNeutral.2] using hr)
        · exact False.elim (by simpa [hNeutral.1] using hr)
      · subst w
        by_cases huOld : u < d
        · exact (prefixReplicaE_last_iff A d u).2 huOld
        · have huFill : u = d := by omega
          subst u
          obtain ⟨r, hr⟩ := hlink
          have hNeutral :=
            (prefixReplicaL_filler_neutral A d v (d + 1)).1 r
          rcases hr with hr | hr
          · exact False.elim (by simpa [hNeutral.1] using hr)
          · exact False.elim (by simpa [hNeutral.2] using hr)

/-- The newly relocated ordinary vertex has free level exactly d,
as required by the definition of a partial type at that cut. -/
theorem prefixReplicaPartialStructure_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v d : Nat) (hv : v < A.size)
    (hd : d ≤ A.freeLevel v) :
    (prefixReplicaPartialStructure A v d hv hd).freeLevel
        (d + 1) = d := by
  exact prefixReplicaE_last_freeLevel A d

/-- The actual FULL partial type of the relocated ordinary vertex
in the constructed partial structure equals the chosen shorter
partial type in the original A. This checks all L facts and E
incidences, not only the crossing binary pattern. -/
theorem prefixReplicaPartialStructure_type_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v d : Nat) (hv : v < A.size)
    (hd : d ≤ A.freeLevel v) :
    (prefixReplicaPartialStructure A v d hv hd).partialTypeAt d
        (d + 1) = A.partialTypeAt d v := by
  let B := prefixReplicaPartialStructure A v d hv hd
  have hBFree : d ≤ B.freeLevel (d + 1) := by
    have hEq := prefixReplicaPartialStructure_freeLevel A v d hv hd
    change B.freeLevel (d + 1) = d at hEq
    omega
  apply PartialTypeWithE.eq_of_atoms
  · exact prefixReplicaL_type_eq A d v
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        calc
          (B.partialTypeAt d (d + 1)).eRelation none none = false :=
            B.partialTypeAt_no_typeE_loop d (d + 1)
          _ = (A.partialTypeAt d v).eRelation none none :=
            (A.partialTypeAt_no_typeE_loop d v).symm
      | some j =>
        calc
          (B.partialTypeAt d (d + 1)).eRelation none (some j) =
              false := B.partialTypeAt_no_reverseE d (d + 1) hBFree j
          _ = (A.partialTypeAt d v).eRelation none (some j) :=
            (A.partialTypeAt_no_reverseE d v hd j).symm
    | some i =>
      cases y with
      | none =>
        exact prefixReplicaE_preserves_type_socle A v d hd i
      | some j =>
        exact prefixReplicaE_preserves_old_socle A d i j

end SuccessorTree.V10
