import SuccessorTree.V10.LocalAgeInsertion
import SuccessorTree.V10.CanonicalInsertionParameter
import Mathlib.Tactic

/-!
# A literal one-coordinate L+ insertion

The boring-extension construction of Lemma 6.51 inserts one coordinate ell.
This file isolates the finite partial-structure bookkeeping. Old L-atoms are
copied through the gap. The new vertex has supplied singleton and crossing
atoms. E is defined by the exact transported free cuts, so downward closure
is automatic.

Two local linkage conditions are sufficient for E3: relations from an old
lower vertex to the insertion must lie below the insertion's own E-cut, and
relations from the insertion to a shifted upper old vertex require that the
old vertex's E-cut reaches ell. Under the usual 0-or-strict cut condition at
the inserted vertex, spacing follows.

This is still only the finite structure transformation. The global Kpt shape
map and the B3 forbidden-age argument are subsequent steps.
-/

namespace SuccessorTree.V10

/-- Complete L-data involving the newly inserted coordinate. -/
structure InsertedLData (db du dd : Nat) where
  loop : Fin db → Bool
  unary : Fin du → Bool
  diagonal : Fin dd → Bool
  incoming : Nat → Fin db → Bool
  outgoing : Nat → Fin db → Bool

/-- Complete target L-reduct after inserting ell. Old coordinates are
renamed through insertAddress; all relations involving ell are explicit. -/
def insertL
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (D : InsertedLData db du dd) :
    AgeTestModel db du dd :=
  { carrier := {x | x < A.size + 1}
    binary := fun x y r =>
      if hx : x = ell then
        if hy : y = ell then D.loop r
        else D.outgoing (removeInserted ell y) r
      else if hy : y = ell then
        D.incoming (removeInserted ell x) r
      else
        A.L.binary (removeInserted ell x) (removeInserted ell y) r
    unary := fun x r =>
      if x = ell then D.unary r
      else A.L.unary (removeInserted ell x) r
    diagonal := fun x r =>
      if x = ell then D.diagonal r
      else A.L.diagonal (removeInserted ell x) r }

/-- The transported free cut of a target coordinate. -/
noncomputable def insertedCut
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d v : Nat) : Nat :=
  if hv : v < ell then A.freeLevel v
  else if heq : v = ell then d
  else
    let f := A.freeLevel (v - 1)
    if f < ell then f else f + 1

@[simp] theorem insertedCut_at
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) :
    insertedCut A ell d ell = d := by
  simp [insertedCut]

/-- An old coordinate's free cut is transported through the same insertion
of a gap: cuts ending before ell are unchanged, all longer cuts grow by one. -/
theorem insertedCut_insertAddress
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d y : Nat) :
    insertedCut A ell d (insertAddress ell y) =
      if A.freeLevel y < ell then A.freeLevel y
      else A.freeLevel y + 1 := by
  by_cases hy : y < ell
  · have hf : A.freeLevel y < ell :=
      lt_of_le_of_lt (A.freeLevel_le y) hy
    simp [insertAddress, hy, insertedCut, hf]
  · have hye : ell ≤ y := Nat.le_of_not_gt hy
    have htarget : ¬ y + 1 < ell := by omega
    have hneq : y + 1 ≠ ell := by omega
    simp [insertAddress, hy, insertedCut, htarget, hneq]

/-- Old membership in a free E-socle is exactly membership after inserting
the coordinate gap. -/
theorem insertAddress_lt_insertedCut_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d x y : Nat) :
    insertAddress ell x < insertedCut A ell d (insertAddress ell y) ↔
      x < A.freeLevel y := by
  rw [insertedCut_insertAddress]
  by_cases hf : A.freeLevel y < ell
  · have hxBelow : x < A.freeLevel y → x < ell :=
      fun h => lt_trans h hf
    constructor
    · intro h
      by_cases hx : x < ell
      · simpa [insertAddress, hx, hf] using h
      · simp [insertAddress, hx, hf] at h
        omega
    · intro h
      simp [insertAddress, hxBelow h, hf, h]
  · constructor
    · intro h
      by_cases hx : x < ell
      · simp [insertAddress, hx, hf] at h
        omega
      · simp [insertAddress, hx, hf] at h
        omega
    · intro h
      by_cases hx : x < ell
      · simp [insertAddress, hx, hf]
        omega
      · simp [insertAddress, hx, hf]
        omega

/-- Exact E relation determined by the transported initial-segment cuts,
clipped to the target finite carrier. -/
noncomputable def insertE
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d u v : Nat) : Bool := by
  classical
  exact decide (v < A.size + 1 ∧ u < insertedCut A ell d v)

theorem insertE_true_iff
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d u v : Nat) :
    insertE A ell d u v = true ↔
      v < A.size + 1 ∧ u < insertedCut A ell d v := by
  classical
  simp [insertE]

/-- Every transported cut lies at or below its target coordinate. -/
theorem insertedCut_le
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d v : Nat)
    (hell : ell ≤ A.size) (hd : d ≤ ell)
    (hv : v < A.size + 1) :
    insertedCut A ell d v ≤ v := by
  by_cases hvl : v < ell
  · simp [insertedCut, hvl]
    exact A.freeLevel_le v
  · by_cases heq : v = ell
    · subst v
      simpa [insertedCut] using hd
    · have hvgt : ell < v := by omega
      have hold : v - 1 < A.size := by omega
      have hf := A.freeLevel_le (v - 1)
      simp [insertedCut, hvl, heq]
      split_ifs <;> omega

/-- A positive transported cut is strictly below its target. This is the
spacing statement at the level of cuts. -/
theorem insertedCut_pos_lt
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d v : Nat)
    (hell : ell ≤ A.size) (hd : d ≤ ell)
    (hdGate : d = 0 ∨ d < ell)
    (hv : v < A.size + 1)
    (hpos : 0 < insertedCut A ell d v) :
    insertedCut A ell d v < v := by
  by_cases hvl : v < ell
  · have hEq : insertedCut A ell d v = A.freeLevel v := by
      simp [insertedCut, hvl]
    rw [hEq] at hpos ⊢
    exact freeLevel_pos_lt_vertex A v hpos
  · by_cases heq : v = ell
    · subst v
      simp only [insertedCut_at] at hpos ⊢
      rcases hdGate with hz | hlt
      · omega
      · exact hlt
    · have hvgt : ell < v := by omega
      have hold : v - 1 < A.size := by omega
      let f := A.freeLevel (v - 1)
      have hfle : f ≤ v - 1 := A.freeLevel_le (v - 1)
      have hfold : 0 < f → f < v - 1 :=
        fun hf => freeLevel_pos_lt_vertex A (v - 1) hf
      have hEq : insertedCut A ell d v =
          (if f < ell then f else f + 1) := by
        simp [insertedCut, hvl, heq, f]
      rw [hEq] at hpos ⊢
      by_cases hfl : f < ell
      · simp [hfl] at hpos ⊢
        exact hfold hpos
      · simp [hfl]
        have hfpos : 0 < f := by omega
        have := hfold hfpos
        omega

/-- Old-old L atoms are copied exactly through insertion. -/
theorem insertL_old_binary
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (D : InsertedLData db du dd)
    (x y : Nat) (r : Fin db) :
    (insertL A ell D).binary
        (insertAddress ell x) (insertAddress ell y) r =
      A.L.binary x y r := by
  have hx : insertAddress ell x ≠ ell := by
    unfold insertAddress
    split <;> omega
  have hy : insertAddress ell y ≠ ell := by
    unfold insertAddress
    split <;> omega
  simp [insertL, hx, hy]

theorem insertL_old_unary
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (D : InsertedLData db du dd)
    (x : Nat) (r : Fin du) :
    (insertL A ell D).unary (insertAddress ell x) r =
      A.L.unary x r := by
  have hx : insertAddress ell x ≠ ell := by
    unfold insertAddress
    split <;> omega
  simp [insertL, hx]

theorem insertL_old_diagonal
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (D : InsertedLData db du dd)
    (x : Nat) (r : Fin dd) :
    (insertL A ell D).diagonal (insertAddress ell x) r =
      A.L.diagonal x r := by
  have hx : insertAddress ell x ≠ ell := by
    unfold insertAddress
    split <;> omega
  simp [insertL, hx,
    insertAddress_removeInserted ell (insertAddress ell x) hx]

/-- Construct one finite partial structure after inserting ell. The two
linkage hypotheses are exactly the E3 obligations involving the new vertex. -/
noncomputable def insertPartial
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (D : InsertedLData db du dd)
    (hell : ell ≤ A.size) (hd : d ≤ ell)
    (hdGate : d = 0 ∨ d < ell)
    (hBelow : ∀ x, x < ell →
      (∃ r : Fin db, D.incoming x r = true ∨ D.outgoing x r = true) →
      x < d)
    (hAbove : ∀ y, ell ≤ y → y < A.size →
      (∃ r : Fin db, D.outgoing y r = true ∨ D.incoming y r = true) →
      ell ≤ A.freeLevel y) :
    EnumeratedPartialStructure db du dd := by
  let L := insertL A ell D
  let E := insertE A ell d
  refine
    { size := A.size + 1
      L := L
      carrier_iff := by intro v; rfl
      E := E
      E_inside := ?_
      spaced := ?_
      downward := ?_
      linked_E := ?_ }
  · intro u v hE
    obtain ⟨hv, hu⟩ := (insertE_true_iff A ell d u v).1 hE
    have hcut := insertedCut_le A ell d v hell hd hv
    exact ⟨lt_trans hu (hcut.trans_lt hv), hv⟩
  · intro u v hE
    obtain ⟨hv, hu⟩ := (insertE_true_iff A ell d u v).1 hE
    have hpos : 0 < insertedCut A ell d v := lt_of_le_of_lt (Nat.zero_le u) hu
    have hcut := insertedCut_pos_lt A ell d v hell hd hdGate hv hpos
    omega
  · intro u v hE w hw
    obtain ⟨hv, hu⟩ := (insertE_true_iff A ell d u v).1 hE
    exact (insertE_true_iff A ell d w v).2
      ⟨hv, lt_trans hw hu⟩
  · intro u v huv hu hv hlink
    by_cases huell : u = ell
    · subst u
      have hvell : ell < v := huv
      let y := removeInserted ell v
      have hvne : v ≠ ell := by omega
      have hyOld : y < A.size := by
        unfold y removeInserted
        simp [Nat.not_lt.mpr (Nat.le_of_lt hvell)]
        omega
      have hyGe : ell ≤ y := by
        unfold y removeInserted
        simp [Nat.not_lt.mpr (Nat.le_of_lt hvell)]
        omega
      have hLinkData :
          ∃ r : Fin db, D.outgoing y r = true ∨ D.incoming y r = true := by
        simpa [L, insertL, hvne, y] using hlink
      have hReach := hAbove y hyGe hyOld hLinkData
      apply (insertE_true_iff A ell d ell v).2
      refine ⟨hv, ?_⟩
      have hvAddr : insertAddress ell y = v :=
        insertAddress_removeInserted ell v (by omega)
      rw [← hvAddr, insertedCut_insertAddress]
      by_cases hf : A.freeLevel y < ell
      · omega
      · simp [hf]
        omega
    · by_cases hvell : v = ell
      · subst v
        have huBelow : u < ell := huv
        let x := removeInserted ell u
        have hxEq : x = u := by
          simp [x, removeInserted, huBelow]
        have hLinkData :
            ∃ r : Fin db, D.incoming u r = true ∨ D.outgoing u r = true := by
          simpa [L, insertL, huell, removeInserted, huBelow] using hlink
        have huCut := hBelow u huBelow hLinkData
        exact (insertE_true_iff A ell d u ell).2
          ⟨by omega, by simpa [insertedCut] using huCut⟩
      · let x := removeInserted ell u
        let y := removeInserted ell v
        have hxAddr : insertAddress ell x = u :=
          insertAddress_removeInserted ell u huell
        have hyAddr : insertAddress ell y = v :=
          insertAddress_removeInserted ell v hvell
        have hxOld : x < A.size := by
          by_cases hxlt : x < ell
          · omega
          · have hsh : insertAddress ell x = x + 1 :=
              insertAddress_above ell x (by omega)
            rw [← hxAddr, hsh] at hu
            omega
        have hyOld : y < A.size := by
          by_cases hylt : y < ell
          · omega
          · have hsh : insertAddress ell y = y + 1 :=
              insertAddress_above ell y (by omega)
            rw [← hyAddr, hsh] at hv
            omega
        have hxy : x < y :=
          removeInserted_lt ell u v huv huell hvell
        have hOldLink :
            ∃ r : Fin db,
              A.L.binary x y r = true ∨ A.L.binary y x r = true := by
          simpa [L, insertL, huell, hvell, x, y] using hlink
        have hOldE := A.linked_E x y hxy hxOld hyOld hOldLink
        apply (insertE_true_iff A ell d u v).2
        refine ⟨hv, ?_⟩
        rw [← hxAddr, ← hyAddr]
        exact (insertAddress_lt_insertedCut_iff A ell d x y).2
          ((A.E_iff_freeLevel x y).1 hOldE)

/-- The constructed insertion satisfies the old-atom interface used by the
forbidden-copy pullback theorem. -/
theorem insertPartial_isLInsertion
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell d : Nat) (D : InsertedLData db du dd)
    (hell : ell ≤ A.size) (hd : d ≤ ell)
    (hdGate : d = 0 ∨ d < ell)
    (hBelow : ∀ x, x < ell →
      (∃ r : Fin db, D.incoming x r = true ∨ D.outgoing x r = true) →
      x < d)
    (hAbove : ∀ y, ell ≤ y → y < A.size →
      (∃ r : Fin db, D.outgoing y r = true ∨ D.incoming y r = true) →
      ell ≤ A.freeLevel y) :
    IsLInsertion A
      (insertPartial A ell d D hell hd hdGate hBelow hAbove) ell := by
  constructor
  · exact hell
  · rfl
  · intro x y hx hy r
    exact insertL_old_binary A ell D x y r
  · intro x hx r
    exact insertL_old_unary A ell D x r
  · intro x hx r
    exact insertL_old_diagonal A ell D x r

end SuccessorTree.V10
