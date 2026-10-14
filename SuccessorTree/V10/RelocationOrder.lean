import SuccessorTree.V10.RelocationIrreducible

/-!
# Ordering and avoidance of the old selected level after relocation

For the age-change signature lemma, lower originals are listed in increasing
first-index order. Replacing their generations by ranks 0, ..., r-1
preserves the numerical order of their H positions, and keeps them
before each prescribed later upper original.

If the original last lower vertex is the tested level ell, with its
generation strictly above r-1, then every relocated lower vertex lies
strictly before ell. Thus the relocated forbidden copy avoids ell once
its unchanged upper vertices are already known to lie above ell.

This is the numerical part only, and does not identify the upper witness
with a node of the actual partial-type tree.
-/

namespace SuccessorTree.V10

/-- Every pair of relocated lower vertices remains in strictly increasing
numeric H order. -/
theorem relocated_lower_order
    {n r : Nat} (k : Nat) (hr : r ≤ k)
    (first : Fin r → Fin n) (hFirst : StrictMono first)
    (a b : Fin r) (hab : a < b) :
    hPosition k (first a).val a.val <
      hPosition k (first b).val b.val := by
  have hak : a.val ≤ k := by
    have ha := a.isLt
    omega
  exact hPosition_lt_of_block_lt k
    (first a).val (first b).val a.val b.val hak
    (Fin.lt_def.mp (hFirst hab))

/-- Each relocated lower original precedes a later real original whose
first index is larger; this is independent of the upper generation. -/
theorem relocated_lower_before_upper
    {n r s : Nat} (k : Nat) (hr : r ≤ k)
    (first : Fin r → Fin n) (upperFirst : Fin s → Fin n)
    (hUpperAfter : ∀ a : Fin r, ∀ b : Fin s,
      first a < upperFirst b)
    (upperGeneration : Fin s → Nat)
    (a : Fin r) (b : Fin s) :
    hPosition k (first a).val a.val <
      hPosition k (upperFirst b).val (upperGeneration b) := by
  have hak : a.val ≤ k := by
    have ha := a.isLt
    omega
  exact hPosition_lt_of_block_lt k
    (first a).val (upperFirst b).val a.val
    (upperGeneration b) hak
    (Fin.lt_def.mp (hUpperAfter a b))

/-- If the last original has generation n_(r-1) > r-1,
all relocated lower vertices lie before that original's old position ell.
The positive-size hypothesis is essential to select the last original. -/
theorem relocated_lower_avoids_old_last
    {n r : Nat} (k : Nat)
    (hr0 : 0 < r) (hr : r ≤ k)
    (first : Fin r → Fin n) (hFirst : StrictMono first)
    (lastGeneration : Nat) (hGap : r - 1 < lastGeneration)
    (a : Fin r) :
    hPosition k (first a).val a.val <
      hPosition k
        (first ⟨r - 1, by omega⟩).val lastGeneration := by
  let last : Fin r := ⟨r - 1, by omega⟩
  have haLe : a.val ≤ last.val := by
    simp [last]
    omega
  rcases lt_or_eq_of_le haLe with haLt | haEq
  · have hlt : a < last := Fin.lt_def.mpr haLt
    have hak : a.val ≤ k := by
      have ha := a.isLt
      omega
    exact hPosition_lt_of_block_lt k
      (first a).val (first last).val a.val lastGeneration
      hak (Fin.lt_def.mp (hFirst hlt))
  · have hae : a = last := Fin.ext haEq
    subst a
    simpa [last] using
      (hPosition_lt_of_gen_lt k (first last).val
        (r - 1) lastGeneration hGap)

end SuccessorTree.V10
