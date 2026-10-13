import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Induced finite L-age transport for the M2 non-edge witness

The last part of the M2 CompatibleB3 proof constructs an explicit
order-preserving induced L embedding of an arbitrary finite age test W
into an ordinary socle of the single image F(X). This module isolates
the finite model consequence: such an embedding transports every
ordered *induced* forbidden realization in either direction.

There is no E here: the age test is in the original L language.
No new age-preservation or M2 axiom is assumed.
-/

namespace SuccessorTree.V10

/-- A literal ordered induced embedding of finite L-age models.
The binary equality is required for DISTINCT vertices, exactly as
in ForbiddenAtomicPattern.Realizes; diagonal L atoms are separate. -/
structure AgeTestModel.InducedEmbedding
    {db du dd : Nat}
    (W V : AgeTestModel db du dd) where
  toFun : Nat → Nat
  strictMono : StrictMono toFun
  inside : ∀ x, x ∈ W.carrier → toFun x ∈ V.carrier
  binary : ∀ x y, x ∈ W.carrier → y ∈ W.carrier → x ≠ y →
    ∀ t : Fin db, V.binary (toFun x) (toFun y) t = W.binary x y t
  unary : ∀ x, x ∈ W.carrier → ∀ t : Fin du,
    V.unary (toFun x) t = W.unary x t
  diagonal : ∀ x, x ∈ W.carrier → ∀ t : Fin dd,
    V.diagonal (toFun x) t = W.diagonal x t

/-- All positive AND negative atoms of an induced forbidden copy
transport along the explicit ordered embedding. -/
theorem AgeTestModel.InducedEmbedding.realizes
    {r db du dd : Nat} {W V : AgeTestModel db du dd}
    (H : W.InducedEmbedding V)
    (P : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat) (hCopy : W.Realizes P f) :
    V.Realizes P (fun a => H.toFun (f a)) := by
  rcases hCopy with ⟨hMono,hIn,hBinary,hUnary,hDiagonal⟩
  refine ⟨H.strictMono.comp hMono,?_,?_,?_,?_⟩
  · intro a
    exact H.inside (f a) (hIn a)
  · intro a b hab t
    have hDistinct : f a ≠ f b := fun h => hab (hMono.injective h)
    exact (H.binary (f a) (f b) (hIn a) (hIn b) hDistinct t).trans
      (hBinary a b hab t)
  · intro a t
    exact (H.unary (f a) (hIn a) t).trans (hUnary a t)
  · intro a t
    exact (H.diagonal (f a) (hIn a) t).trans (hDiagonal a t)

/-- A normalized irreducible forbidden family is hereditary under
all literal ordered induced embeddings. No E-expansion of W needed. -/
theorem AgeTestModel.InducedEmbedding.preserves_avoidance
    {db du dd : Nat} {W V : AgeTestModel db du dd}
    (H : W.InducedEmbedding V)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids V) :
    ∀ bad, bad ∈ family → bad.Avoids W := by
  intro bad hBad
  cases bad with
  | singleton P hNeutral =>
      rintro ⟨f,hCopy⟩
      exact hAvoid (.singleton P hNeutral) hBad
        ⟨_,H.realizes P f hCopy⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨f,hCopy⟩
      exact hAvoid (.nontrivial r P hr hIrred) hBad
        ⟨_,H.realizes P f hCopy⟩

end SuccessorTree.V10
