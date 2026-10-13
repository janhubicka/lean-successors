import SuccessorTree.V10.M2BoundedCopySourceAge
import Mathlib.Tactic

/-!
# Complete L-atom records on the real vertices of the bounded M2 source

The sparse source for a forbidden-copy argument contains genuine selected
vertices and neutral fillers. Every directed positive or negative L-atom
between real vertices, and every singleton atom of a real vertex, is
literally the corresponding target atom. The upper--upper pair record
MUST be retained: neutralization is allowed only at unused filler slots.

This does not assert the subsequent E-lift or the final B3 comparison.
-/

namespace SuccessorTree.V10

theorem boundedCopySourceAge_real_binary
    {db du dd : Nat} (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (x y : Nat) (hxN : x < n+r) (hyN : y < n+r)
    (hx : boundedCopyReal n m r e x)
    (hy : boundedCopyReal n m r e y) (t : Fin db) :
    (boundedCopySourceAge V lambda n m r e).binary x y t =
      V.binary (boundedCopyAddress lambda n r e x)
        (boundedCopyAddress lambda n r e y) t := by
  exact AgeTestModel.fillNeutralCarrier_old_binary
    (V.sparsePullback (n+r) (boundedCopyReal n m r e)
      (boundedCopyAddress lambda n r e)) (n+r) x y
    ⟨hxN,hx⟩ ⟨hyN,hy⟩ t

theorem boundedCopySourceAge_real_unary
    {db du dd : Nat} (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (x : Nat) (hxN : x < n+r)
    (hx : boundedCopyReal n m r e x) (t : Fin du) :
    (boundedCopySourceAge V lambda n m r e).unary x t =
      V.unary (boundedCopyAddress lambda n r e x) t := by
  exact AgeTestModel.fillNeutralCarrier_old_unary
    (V.sparsePullback (n+r) (boundedCopyReal n m r e)
      (boundedCopyAddress lambda n r e)) (n+r) x
    ⟨hxN,hx⟩ t

theorem boundedCopySourceAge_real_diagonal
    {db du dd : Nat} (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (x : Nat) (hxN : x < n+r)
    (hx : boundedCopyReal n m r e x) (t : Fin dd) :
    (boundedCopySourceAge V lambda n m r e).diagonal x t =
      V.diagonal (boundedCopyAddress lambda n r e x) t := by
  exact AgeTestModel.fillNeutralCarrier_old_diagonal
    (V.sparsePullback (n+r) (boundedCopyReal n m r e)
      (boundedCopyAddress lambda n r e)) (n+r) x
    ⟨hxN,hx⟩ t

/-- This preserves all upper--upper relations of the alleged forbidden
copy, including both directions and their complements. -/
theorem boundedCopySourceAge_upper_pair
    {db du dd : Nat} (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (a b : Fin r) (ha : m < e a) (hb : m < e b)
    (t : Fin db) :
    (boundedCopySourceAge V lambda n m r e).binary
      (n+a.val) (n+b.val) t = V.binary (e a) (e b) t := by
  have haReal : boundedCopyReal n m r e (n+a.val) :=
    Or.inr ⟨a,rfl,ha⟩
  have hbReal : boundedCopyReal n m r e (n+b.val) :=
    Or.inr ⟨b,rfl,hb⟩
  rw [boundedCopySourceAge_real_binary V lambda n m r e
    (n+a.val) (n+b.val) (by omega) (by omega) haReal hbReal]
  simp only [boundedCopyAddress_upper]

/-- Both orientations of every lower--upper pair are retained. -/
theorem boundedCopySourceAge_low_upper
    {db du dd : Nat} (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (i : Nat) (hi : i < n) (a : Fin r) (ha : m < e a)
    (t : Fin db) :
    (boundedCopySourceAge V lambda n m r e).binary i (n+a.val) t =
        V.binary (lambda i) (e a) t ∧
      (boundedCopySourceAge V lambda n m r e).binary (n+a.val) i t =
        V.binary (e a) (lambda i) t := by
  have hiReal : boundedCopyReal n m r e i := Or.inl hi
  have haReal : boundedCopyReal n m r e (n+a.val) :=
    Or.inr ⟨a,rfl,ha⟩
  constructor
  · rw [boundedCopySourceAge_real_binary V lambda n m r e
      i (n+a.val) (by omega) (by omega) hiReal haReal]
    simp only [boundedCopyAddress_low lambda n r e i hi,
      boundedCopyAddress_upper]
  · rw [boundedCopySourceAge_real_binary V lambda n m r e
      (n+a.val) i (by omega) (by omega) haReal hiReal]
    simp only [boundedCopyAddress_low lambda n r e i hi,
      boundedCopyAddress_upper]

theorem boundedCopySourceAge_upper_singletons
    {db du dd : Nat} (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (a : Fin r) (ha : m < e a) :
    (∀ t : Fin du,
      (boundedCopySourceAge V lambda n m r e).unary (n+a.val) t =
        V.unary (e a) t) ∧
      (∀ t : Fin dd,
      (boundedCopySourceAge V lambda n m r e).diagonal (n+a.val) t =
        V.diagonal (e a) t) := by
  have haReal : boundedCopyReal n m r e (n+a.val) :=
    Or.inr ⟨a,rfl,ha⟩
  constructor
  · intro t
    rw [boundedCopySourceAge_real_unary V lambda n m r e
      (n+a.val) (by omega) haReal]
    simp only [boundedCopyAddress_upper]
  · intro t
    rw [boundedCopySourceAge_real_diagonal V lambda n m r e
      (n+a.val) (by omega) haReal]
    simp only [boundedCopyAddress_upper]

end SuccessorTree.V10
