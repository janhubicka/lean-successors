import SuccessorTree.V10.M2BoundedCopySourceAge
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The L-age input obtained from an alleged forbidden copy

Take a finite target L witness W, its forbidden copy e, and the
one level m deleted by the first M2 factor. The initial source
coordinates map below m. Every source upper position whose copy
index e(a) lies above m maps into W without m. By the explicit
bounded-copy pullback, this produces one finite forbidden-free
dense source L model (with neutral unused slots).

Crucially: no arbitrary E-expansion of W is requested. The E
structure enters only later, by the verified non-edge padding
constructor using the common source socle.
-/

namespace SuccessorTree.V10

/-- Extract the dense, forbidden-free source L-age model for a
single forbidden induced copy, assuming W without m is F-free.
This theorem uses exactly the four finite-age inputs and no
M2 factorization, B3 necessity or abstract amalgamation. -/
theorem boundedCopySourceAge_avoids_from_forbidden_copy
    {r db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (W : AgeTestModel db du dd)
    (P : ForbiddenAtomicPattern r db du dd)
    (e : Fin r → Nat)
    (hCopy : W.Realizes P e)
    (lambda : Nat → Nat)
    (n m : Nat)
    (hLambda : StrictMono lambda)
    (hBelow : ∀ i, i < n → lambda i < m)
    (hInitial : ∀ i, i < m → i ∈ W.carrier)
    (hWithout : ∀ bad, bad ∈ family →
      bad.Avoids (W.withoutVertex m)) :
    ∀ bad, bad ∈ family →
      bad.Avoids
        (boundedCopySourceAge (W.withoutVertex m)
          lambda n m r e) := by
  apply boundedCopySourceAge_avoids family (W.withoutVertex m)
    lambda n m r e hLambda hCopy.1 hBelow
  · intro i hi
    have hLow : lambda i < m := hBelow i hi
    change lambda i ∈ W.carrier ∧ lambda i ≠ m
    exact ⟨hInitial (lambda i) hLow,by omega⟩
  · intro a ha
    change e a ∈ W.carrier ∧ e a ≠ m
    exact ⟨hCopy.2.1 a,by omega⟩
  · exact hWithout

end SuccessorTree.V10
