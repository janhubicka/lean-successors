import SuccessorTree.V10.ActualCrossingSignature
import Mathlib.Tactic

/-!
# Coordinate insertion: forbidden copies away from the new level pull back

Lemma 6.51 inserts one ordinary coordinate ell into every partial type.
Before checking the prescribed crossing at ell, one basic fact should be
literal: an ordered induced forbidden copy which avoids ell is already a
copy in the source structure obtained by deleting that coordinate.

This module proves that statement for complete binary/unary/diagonal
L-reducts. It uses no irreducibility and no auxiliary E relation. Thus the
later age argument can focus solely on forbidden copies containing ell.
-/

namespace SuccessorTree.V10

/-- Address of an old coordinate after inserting a new coordinate at ell. -/
def insertAddress (ell x : Nat) : Nat :=
  if x < ell then x else x + 1

/-- Remove the inserted gap from a target coordinate distinct from ell. -/
def removeInserted (ell y : Nat) : Nat :=
  if y < ell then y else y - 1

@[simp] theorem insertAddress_below (ell x : Nat) (hx : x < ell) :
    insertAddress ell x = x := by simp [insertAddress, hx]

@[simp] theorem insertAddress_above (ell x : Nat) (hx : ell ≤ x) :
    insertAddress ell x = x + 1 := by
  simp [insertAddress, Nat.not_lt.mpr hx]

theorem insertAddress_strictMono (ell : Nat) :
    StrictMono (insertAddress ell) := by
  intro x y hxy
  by_cases hx : x < ell
  · by_cases hy : y < ell
    · simp [insertAddress, hx, hy, hxy]
    · simp [insertAddress, hx, hy]
      omega
  · have hy : ¬ y < ell := by omega
    simp [insertAddress, hx, hy]
    omega

theorem insertAddress_removeInserted
    (ell y : Nat) (hy : y ≠ ell) :
    insertAddress ell (removeInserted ell y) = y := by
  unfold removeInserted
  by_cases hyl : y < ell
  · simp [hyl, insertAddress]
  · have hye : ell < y := by omega
    have hnot : ¬ y - 1 < ell := by omega
    simp [hyl, insertAddress, hnot]
    omega

@[simp] theorem removeInserted_insertAddress
    (ell x : Nat) :
    removeInserted ell (insertAddress ell x) = x := by
  by_cases hx : x < ell
  · simp [removeInserted, insertAddress, hx]
  · have hnot : ¬ x + 1 < ell := by omega
    simp [removeInserted, insertAddress, hx, hnot]

theorem removeInserted_lt
    (ell x y : Nat) (hxy : x < y) (hx : x ≠ ell) (hy : y ≠ ell) :
    removeInserted ell x < removeInserted ell y := by
  by_cases hxl : x < ell
  · by_cases hyl : y < ell
    · simp [removeInserted, hxl, hyl, hxy]
    · simp [removeInserted, hxl, hyl]
      have hey : ell < y := by omega
      omega
  · have hex : ell < x := by omega
    have hyl : ¬ y < ell := by omega
    simp [removeInserted, hxl, hyl]
    omega

/-- The target's old coordinates carry exactly the source L-atoms.
The source/target sizes are included so carrier membership also transports. -/
structure IsLInsertion
    {db du dd : Nat}
    (A B : EnumeratedPartialStructure db du dd)
    (ell : Nat) : Prop where
  level_le : ell ≤ A.size
  size_eq : B.size = A.size + 1
  binary : ∀ x y, x < A.size → y < A.size → ∀ r : Fin db,
    B.L.binary (insertAddress ell x) (insertAddress ell y) r =
      A.L.binary x y r
  unary : ∀ x, x < A.size → ∀ r : Fin du,
    B.L.unary (insertAddress ell x) r = A.L.unary x r
  diagonal : ∀ x, x < A.size → ∀ r : Fin dd,
    B.L.diagonal (insertAddress ell x) r = A.L.diagonal x r

/-- A target coordinate in the finite carrier and distinct from the inserted
coordinate has a valid old source address. -/
theorem IsLInsertion.removeInserted_inside
    {db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd} {ell y : Nat}
    (h : IsLInsertion A B ell)
    (hyB : y < B.size) (hy : y ≠ ell) :
    removeInserted ell y < A.size := by
  rw [h.size_eq] at hyB
  unfold removeInserted
  by_cases hyl : y < ell
  · have hle := h.level_le
    simp [hyl]
    omega
  · simp [hyl]
    omega

/-- A complete ordered induced copy in the target which avoids the inserted
coordinate projects to the source. Positive and negative atoms all transport. -/
theorem IsLInsertion.realizes_away_projects
    {r db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd}
    {ell : Nat} (h : IsLInsertion A B ell)
    (F : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat) (hCopy : B.L.Realizes F f)
    (hAway : ∀ a, f a ≠ ell) :
    A.L.Realizes F (fun a => removeInserted ell (f a)) := by
  obtain ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩ := hCopy
  have hOld : ∀ a, removeInserted ell (f a) < A.size := by
    intro a
    exact h.removeInserted_inside
      ((B.carrier_iff (f a)).1 (hIn a)) (hAway a)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact removeInserted_lt ell (f a) (f b)
      (hMono hab) (hAway a) (hAway b)
  · intro a
    exact (A.carrier_iff _).2 (hOld a)
  · intro a b hab t
    let x := removeInserted ell (f a)
    let y := removeInserted ell (f b)
    have hx : insertAddress ell x = f a :=
      insertAddress_removeInserted ell (f a) (hAway a)
    have hy : insertAddress ell y = f b :=
      insertAddress_removeInserted ell (f b) (hAway b)
    have hAtom := h.binary x y (hOld a) (hOld b) t
    rw [hx, hy] at hAtom
    exact hAtom.symm.trans (hBinary a b hab t)
  · intro a t
    let x := removeInserted ell (f a)
    have hx : insertAddress ell x = f a :=
      insertAddress_removeInserted ell (f a) (hAway a)
    have hAtom := h.unary x (hOld a) t
    rw [hx] at hAtom
    exact hAtom.symm.trans (hUnary a t)
  · intro a t
    let x := removeInserted ell (f a)
    have hx : insertAddress ell x = f a :=
      insertAddress_removeInserted ell (f a) (hAway a)
    have hAtom := h.diagonal x (hOld a) t
    rw [hx] at hAtom
    exact hAtom.symm.trans (hDiagonal a t)

/-- Insertion of old L-atoms cannot create any normalized forbidden copy
which avoids the new coordinate. The only remaining obstruction for
Lemma 6.51 is a forbidden copy containing ell. -/
theorem IsLInsertion.forbidden_copy_contains_inserted
    {db du dd : Nat}
    {A B : EnumeratedPartialStructure db du dd} {ell : Nat}
    (h : IsLInsertion A B ell)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (bad : NormalizedForbidden db du dd) (hbad : bad ∈ family)
    (hCopy : ¬ bad.Avoids B.L) :
    match bad with
    | .singleton F _ =>
        ∀ f : Fin 1 → Nat, B.L.Realizes F f → ∃ a, f a = ell
    | .nontrivial r F _ _ =>
        ∀ f : Fin r → Nat, B.L.Realizes F f → ∃ a, f a = ell := by
  cases bad with
  | singleton F hNeutral =>
      intro f hf
      by_contra hnone
      have hAway : ∀ a, f a ≠ ell := by
        intro a ha
        exact hnone ⟨a, ha⟩
      exact (hAvoid (.singleton F hNeutral) hbad)
        ⟨_, h.realizes_away_projects F f hf hAway⟩
  | nontrivial r F hr hIrred =>
      intro f hf
      by_contra hnone
      have hAway : ∀ a, f a ≠ ell := by
        intro a ha
        exact hnone ⟨a, ha⟩
      exact (hAvoid (.nontrivial r F hr hIrred) hbad)
        ⟨_, h.realizes_away_projects F f hf hAway⟩

end SuccessorTree.V10
