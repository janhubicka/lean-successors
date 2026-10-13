import SuccessorTree.V10.NonedgePadding
import Mathlib.Tactic

/-!
# Ordered coordinates for the final M2 forbidden-copy contradiction

Vertices of a putative forbidden copy at or below the gap coordinate m
remain in place. Selected vertices above m are sent to the level-map
images of their spaced source witness positions. The map is strictly
increasing without any assumptions about L or E; the atom comparison
will be proved separately.
-/
namespace SuccessorTree.V10

/-- Copy the lower part literally and transport only the upper selected
vertices through the genuine source spacing and level map. -/
def m2ForbiddenCopyImage
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (a : Fin r) : Nat :=
  if e a ≤ m then e a
  else lambda (NonedgePadding.address n (n+a.val))

@[simp] theorem m2ForbiddenCopyImage_lower
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (a : Fin r) (ha : e a ≤ m) :
    m2ForbiddenCopyImage lambda n m r e a = e a := by
  simp [m2ForbiddenCopyImage,ha]

@[simp] theorem m2ForbiddenCopyImage_upper
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (a : Fin r) (ha : m < e a) :
    m2ForbiddenCopyImage lambda n m r e a =
      lambda (NonedgePadding.address n (n+a.val)) := by
  have h : ¬ e a ≤ m := by omega
  simp [m2ForbiddenCopyImage,h]

private theorem paddedUpperAddress (n a : Nat) :
    NonedgePadding.address n (n+a) = n+1+2*a := by
  have h : ¬ n+a < n := by omega
  simp [NonedgePadding.address,h]

/-- Image of every selected upper vertex is strictly above m, without
any requirement that it coincide with the original e(a) address. -/
theorem m2ForbiddenCopyImage_upper_gt
    (lambda : Nat → Nat) (hLambda : StrictMono lambda)
    (n m r : Nat) (e : Fin r → Nat) (a : Fin r)
    (hGap : m < lambda n) (ha : m < e a) :
    m < m2ForbiddenCopyImage lambda n m r e a := by
  rw [m2ForbiddenCopyImage_upper lambda n m r e a ha]
  have hIndex : n ≤ NonedgePadding.address n (n+a.val) := by
    rw [paddedUpperAddress]
    omega
  exact lt_of_lt_of_le hGap (hLambda.monotone hIndex)

/-- The final copy positions keep the strict order of the alleged
forbidden copy. The gap is respected across the lower/upper cut. -/
theorem m2ForbiddenCopyImage_strictMono
    (lambda : Nat → Nat) (hLambda : StrictMono lambda)
    (n m r : Nat) (e : Fin r → Nat) (hE : StrictMono e)
    (hGap : m < lambda n) :
    StrictMono (m2ForbiddenCopyImage lambda n m r e) := by
  intro a b hab
  have habE : e a < e b := hE hab
  by_cases ha : e a ≤ m
  · by_cases hb : e b ≤ m
    · simpa [m2ForbiddenCopyImage_lower lambda n m r e a ha,
        m2ForbiddenCopyImage_lower lambda n m r e b hb] using habE
    · have hb' : m < e b := by omega
      rw [m2ForbiddenCopyImage_lower lambda n m r e a ha,
          m2ForbiddenCopyImage_upper lambda n m r e b hb']
      have hHigh : m < lambda (NonedgePadding.address n (n+b.val)) := by
        have hIndex : n ≤ NonedgePadding.address n (n+b.val) := by
          rw [paddedUpperAddress]
          omega
        exact lt_of_lt_of_le hGap (hLambda.monotone hIndex)
      omega
  · have ha' : m < e a := by omega
    have hb' : m < e b := by omega
    rw [m2ForbiddenCopyImage_upper lambda n m r e a ha',
        m2ForbiddenCopyImage_upper lambda n m r e b hb']
    have hAddr : NonedgePadding.address n (n+a.val) <
        NonedgePadding.address n (n+b.val) := by
      rw [paddedUpperAddress,paddedUpperAddress]
      have h : a.val < b.val := hab
      omega
    exact hLambda hAddr

end SuccessorTree.V10
