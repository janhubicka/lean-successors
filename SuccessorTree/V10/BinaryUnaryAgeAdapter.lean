import SuccessorTree.V10.SignatureCollision
import Mathlib.Tactic

/-!
# Original finite unary/binary languages as normalized L records

Theorem 6.26 of successor v10 quantifies over finite signatures
whose symbols have arity one or two. There is no need for a
higher-arity adapter in the current verification pass.

For an original ordered binary predicate B(x,y,r), the normalized
AgeTestModel stores B on DISTINCT arguments in the directed binary
field and B(x,x,r) in its diagonal field. Unary predicates are
stored verbatim. The forbidden-pattern record has exactly the
same split. Consequently AgeTestModel.Realizes of the encoded
pattern is equivalent to the usual induced ordered embedding
condition on ALL ordered binary pairs, including equal arguments,
and all unary symbols. Both present and absent atoms are
retained, and no symmetry is imposed.

This proves the elementary language dictionary used by the
universal transfer; it does not itself establish model-theoretic
universality or the enumerated K→G+ embedding.
-/

namespace SuccessorTree.V10

/-- Encode an arbitrary original finite unary/binary signature
as the normalized distinct-pair/unary/diagonal Boolean model. -/
def binaryUnaryAgeModel
    {db du : Nat}
    (carrier : Set Nat)
    (B : Nat → Nat → Fin db → Bool)
    (U : Nat → Fin du → Bool) :
    AgeTestModel db du db :=
  { carrier := carrier
    binary := B
    unary := U
    diagonal := fun x a => B x x a }

/-- Encode the original forbidden finite ordered pattern in
the SAME distinct-pair/unary/diagonal representation. -/
def binaryUnaryForbiddenPattern
    {r db du : Nat}
    (B : Fin r → Fin r → Fin db → Bool)
    (U : Fin r → Fin du → Bool) :
    ForbiddenAtomicPattern r db du db :=
  { binary := B
    unary := U
    diagonal := fun x a => B x x a }

/-- Exact equivalence of original-language induced ordered
embeddings and normalized complete-record Realizes, including
diagonal binary atoms and absent directed tuples. -/
theorem binaryUnary_realizes_iff
    {r db du : Nat}
    (carrier : Set Nat)
    (B : Nat → Nat → Fin db → Bool)
    (U : Nat → Fin du → Bool)
    (PB : Fin r → Fin r → Fin db → Bool)
    (PU : Fin r → Fin du → Bool)
    (f : Fin r → Nat) :
    (binaryUnaryAgeModel carrier B U).Realizes
      (binaryUnaryForbiddenPattern PB PU) f ↔
    StrictMono f ∧
      (∀ a : Fin r, f a ∈ carrier) ∧
      (∀ a b : Fin r, ∀ t : Fin db,
        B (f a) (f b) t = PB a b t) ∧
      (∀ a : Fin r, ∀ t : Fin du,
        U (f a) t = PU a t) := by
  constructor
  · rintro ⟨hMono,hCarrier,hOff,hUnary,hDiag⟩
    refine ⟨hMono,hCarrier,?_,hUnary⟩
    intro a b t
    by_cases hab : a = b
    · subst b
      exact hDiag a t
    · exact hOff a b hab t
  · rintro ⟨hMono,hCarrier,hBinary,hUnary⟩
    refine ⟨hMono,hCarrier,?_,hUnary,?_⟩
    · intro a b hab t
      exact hBinary a b t
    · intro a t
      exact hBinary a a t

end SuccessorTree.V10