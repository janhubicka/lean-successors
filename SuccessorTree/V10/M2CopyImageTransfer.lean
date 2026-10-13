import SuccessorTree.V10.M2CopyImageCoordinates
import Mathlib.Tactic

/-!
# Atom-by-atom final comparison in the M2 forbidden-copy argument

The source/image part of B3 must prove complete equality of atoms, not
only preservation of positive edges. This is the final assembly lemma:
once the three lower/upper zones have been compared, the alleged ordered
induced forbidden copy transfers into the image type's L-age model.
The remaining F-specific comparisons are *hypotheses* here, not axioms.
-/

namespace SuccessorTree.V10

/-- Transfer a finite induced ordered pattern along the concrete mixed
image coordinates. Every binary equality covers both positive and
negative directed atoms. Unary and diagonal facts are independent
obligations, so singleton obstructions are included. -/
theorem m2ForbiddenCopy_realizes_of_atomwise
    {r db du dd : Nat}
    (P : ForbiddenAtomicPattern r db du dd)
    (W V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m : Nat) (e : Fin r → Nat)
    (hLambda : StrictMono lambda) (hGap : m < lambda n)
    (hCopy : W.Realizes P e)
    (hInside : ∀ a : Fin r,
      m2ForbiddenCopyImage lambda n m r e a ∈ V.carrier)
    (hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      V.binary (m2ForbiddenCopyImage lambda n m r e a)
        (m2ForbiddenCopyImage lambda n m r e b) t =
          W.binary (e a) (e b) t)
    (hUnary : ∀ a : Fin r, ∀ t : Fin du,
      V.unary (m2ForbiddenCopyImage lambda n m r e a) t =
        W.unary (e a) t)
    (hDiagonal : ∀ a : Fin r, ∀ t : Fin dd,
      V.diagonal (m2ForbiddenCopyImage lambda n m r e a) t =
        W.diagonal (e a) t) :
    V.Realizes P (m2ForbiddenCopyImage lambda n m r e) := by
  refine ⟨m2ForbiddenCopyImage_strictMono lambda hLambda n m r e
      hCopy.1 hGap, hInside, ?_, ?_, ?_⟩
  · intro a b hab t
    exact (hBinary a b hab t).trans (hCopy.2.2.1 a b hab t)
  · intro a t
    exact (hUnary a t).trans (hCopy.2.2.2.1 a t)
  · intro a t
    exact (hDiagonal a t).trans (hCopy.2.2.2.2 a t)

/-- All four configurations of a pair relative to the gap are enough
to supply the exact binary comparison required above. -/
theorem m2ForbiddenCopy_binary_of_zones
    {r db du dd : Nat}
    (W V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m : Nat) (e : Fin r → Nat)
    (hLowLow : ∀ a b : Fin r, a ≠ b → e a ≤ m → e b ≤ m →
      ∀ t : Fin db, V.binary (e a) (e b) t = W.binary (e a) (e b) t)
    (hLowHigh : ∀ a b : Fin r, a ≠ b → e a ≤ m → m < e b →
      ∀ t : Fin db,
      V.binary (e a) (lambda (NonedgePadding.address n (n+b.val))) t =
        W.binary (e a) (e b) t)
    (hHighLow : ∀ a b : Fin r, a ≠ b → m < e a → e b ≤ m →
      ∀ t : Fin db,
      V.binary (lambda (NonedgePadding.address n (n+a.val))) (e b) t =
        W.binary (e a) (e b) t)
    (hHighHigh : ∀ a b : Fin r, a ≠ b → m < e a → m < e b →
      ∀ t : Fin db,
      V.binary (lambda (NonedgePadding.address n (n+a.val)))
        (lambda (NonedgePadding.address n (n+b.val))) t =
          W.binary (e a) (e b) t) :
    ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      V.binary (m2ForbiddenCopyImage lambda n m r e a)
        (m2ForbiddenCopyImage lambda n m r e b) t =
          W.binary (e a) (e b) t := by
  intro a b hab t
  by_cases ha : e a ≤ m
  · by_cases hb : e b ≤ m
    · simpa [m2ForbiddenCopyImage_lower lambda n m r e a ha,
        m2ForbiddenCopyImage_lower lambda n m r e b hb] using
        hLowLow a b hab ha hb t
    · have hb' : m < e b := by omega
      simpa [m2ForbiddenCopyImage_lower lambda n m r e a ha,
        m2ForbiddenCopyImage_upper lambda n m r e b hb'] using
        hLowHigh a b hab ha hb' t
  · have ha' : m < e a := by omega
    by_cases hb : e b ≤ m
    · simpa [m2ForbiddenCopyImage_upper lambda n m r e a ha',
        m2ForbiddenCopyImage_lower lambda n m r e b hb] using
        hHighLow a b hab ha' hb t
    · have hb' : m < e b := by omega
      simpa [m2ForbiddenCopyImage_upper lambda n m r e a ha',
        m2ForbiddenCopyImage_upper lambda n m r e b hb'] using
        hHighHigh a b hab ha' hb' t

end SuccessorTree.V10
