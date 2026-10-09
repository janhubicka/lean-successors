import SuccessorTree.V10.SignatureProfiles

/-!
# Exact full L-types through a finite socle

A finite unary/binary signature records unary and diagonal singleton
atoms, plus both ordered orientations of every binary atom joining the type
vertex to a numbered socle vertex. This is the elementary data required
for the "type through ell+1" sentences in the v10 signature proof.

Equality of those records at a common shorter cut automatically gives
the two cross-atom equalities used by the splice. This does not yet prove
that the concrete KFpt successor/partial-type records agree with this
coding: that is the remaining mathematical adapter.
-/

namespace SuccessorTree.V10

/-- All singleton and cross-socle atoms of a type vertex, including both
orientations of every binary symbol. -/
structure FullAtomicTypePrefix (cut db du dd : Nat) where
  unary : Fin du → Bool
  diagonal : Fin dd → Bool
  fromSocle : Fin cut → Fin db → Bool
  toSocle : Fin cut → Fin db → Bool

/-- Actual full directed atomic record extracted from a finite
age-test structure up to an initial socle cut. -/
def fullAtomicTypePrefix {db du dd : Nat}
    (B : Nat → Nat → Fin db → Bool)
    (U : Nat → Fin du → Bool)
    (D : Nat → Fin dd → Bool)
    (cut upper : Nat) : FullAtomicTypePrefix cut db du dd :=
  { unary := U upper
    diagonal := D upper
    fromSocle := fun x t => B x.val upper t
    toSocle := fun x t => B upper x.val t }

/-- A full type agreement through a cut entails equality of both directed
binary atom vectors with each earlier socle vertex. In particular, it
retains the coordinate at the smaller tested level. -/
theorem fullAtomicTypePrefix_cross
    {db du dd : Nat}
    (B0 B1 : Nat → Nat → Fin db → Bool)
    (U0 U1 : Nat → Fin du → Bool)
    (D0 D1 : Nat → Fin dd → Bool)
    (cut lower upper0 upper1 : Nat) (hLower : lower < cut)
    (hType :
      fullAtomicTypePrefix B0 U0 D0 cut upper0 =
      fullAtomicTypePrefix B1 U1 D1 cut upper1)
    (t : Fin db) :
    B0 lower upper0 t = B1 lower upper1 t ∧
    B0 upper0 lower t = B1 upper1 lower t := by
  have hForward := congrArg
    (fun p : FullAtomicTypePrefix cut db du dd =>
      p.fromSocle ⟨lower, hLower⟩ t) hType
  have hBackward := congrArg
    (fun p : FullAtomicTypePrefix cut db du dd =>
      p.toSocle ⟨lower, hLower⟩ t) hType
  exact ⟨hForward, hBackward⟩

/-- The exact prefix-type formulation of the missing cross-relations
step in Observation 6.52. The hypothesis is equality of COMPLETE
binary/unary/diagonal types on every coordinate strictly below cut,
where cut is to be instantiated as ell0+1. Equality only through ell0
would omit precisely the coordinate being tested. -/
theorem signatureSplice_cross_of_fullTypePrefixes
    {r M db du dd : Nat}
    (signature : Fin r → Option (Fin M))
    (earlier later : Fin r → Nat)
    (B0 B1 : Nat → Nat → Fin db → Bool)
    (U0 U1 : Nat → Fin du → Bool)
    (D0 D1 : Nat → Fin dd → Bool)
    (cut : Nat)
    (hLower : ∀ a, signature a = none → earlier a < cut)
    (hUpperType : ∀ b, signature b ≠ none →
      fullAtomicTypePrefix B0 U0 D0 cut (earlier b) =
        fullAtomicTypePrefix B1 U1 D1 cut (later b)) :
    ∀ a b : Fin r, a ≠ b →
      signature a = none → signature b ≠ none → ∀ t : Fin db,
        B1 (earlier a) (later b) t =
          B0 (earlier a) (earlier b) t ∧
        B1 (later b) (earlier a) t =
          B0 (earlier b) (earlier a) t := by
  intro a b _ ha hb t
  obtain ⟨hForward, hBackward⟩ :=
    fullAtomicTypePrefix_cross B0 B1 U0 U1 D0 D1
      cut (earlier a) (earlier b) (later b)
      (hLower a ha) (hUpperType b hb) t
  exact ⟨hForward.symm, hBackward.symm⟩

end SuccessorTree.V10
