import SuccessorTree.V10.M2NeutralCarrierFill
import Mathlib.Tactic

/-!
# Induced finite age pullbacks on a sparse selected carrier

For the M2 non-edge witness, only the upper vertices belonging to
one putative forbidden copy must be realized. Other numerical slots
are neutral fillers. Their images need not be ordered at all: only
the genuine selected carrier must be mapped by an increasing induced
L-embedding.

This section proves age avoidance for this exact situation without
using auxiliary E, a new age axiom, or any M2 hypothesis. Together
with the neutral-carrier completion theorem, it converts sparse
copies into a dense initial ordinal source model acceptable to the
existing NonedgePadding construction.
-/

namespace SuccessorTree.V10

/-- An ordered induced L embedding restricted to its ACTUAL carrier.
No monotonicity is demanded at nonvertices, allowing dummy addresses. -/
structure AgeTestModel.InducedEmbeddingOnCarrier
    {db du dd : Nat}
    (W V : AgeTestModel db du dd) where
  toFun : Nat → Nat
  order : ∀ x y, x ∈ W.carrier → y ∈ W.carrier → x < y →
    toFun x < toFun y
  inside : ∀ x, x ∈ W.carrier → toFun x ∈ V.carrier
  binary : ∀ x y, x ∈ W.carrier → y ∈ W.carrier → x ≠ y →
    ∀ t : Fin db, V.binary (toFun x) (toFun y) t = W.binary x y t
  unary : ∀ x, x ∈ W.carrier → ∀ t : Fin du,
    V.unary (toFun x) t = W.unary x t
  diagonal : ∀ x, x ∈ W.carrier → ∀ t : Fin dd,
    V.diagonal (toFun x) t = W.diagonal x t

/-- Full positive/negative induced pattern realization transports
even when the embedding is ordered only ON the actual carrier. -/
theorem AgeTestModel.InducedEmbeddingOnCarrier.realizes
    {r db du dd : Nat}
    {W V : AgeTestModel db du dd}
    (H : W.InducedEmbeddingOnCarrier V)
    (P : ForbiddenAtomicPattern r db du dd)
    (f : Fin r → Nat) (hCopy : W.Realizes P f) :
    V.Realizes P (fun a => H.toFun (f a)) := by
  rcases hCopy with ⟨hMono,hIn,hBinary,hUnary,hDiagonal⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro a b hab
    exact H.order (f a) (f b) (hIn a) (hIn b) (hMono hab)
  · intro a
    exact H.inside (f a) (hIn a)
  · intro a b hab t
    have hNe : f a ≠ f b := fun h => hab (hMono.injective h)
    exact (H.binary (f a) (f b) (hIn a) (hIn b) hNe t).trans
      (hBinary a b hab t)
  · intro a t
    exact (H.unary (f a) (hIn a) t).trans (hUnary a t)
  · intro a t
    exact (H.diagonal (f a) (hIn a) t).trans (hDiagonal a t)

/-- Avoidance descends along a carrier-relative induced embedding for
every normalized forbidden pattern, including non-neutral singletons. -/
theorem AgeTestModel.InducedEmbeddingOnCarrier.preserves_avoidance
    {db du dd : Nat}
    {W V : AgeTestModel db du dd}
    (H : W.InducedEmbeddingOnCarrier V)
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

/-- Pull back the L atoms of a target onto a finite (possibly sparse)
set of genuine source indices, with arbitrary dummy positions. -/
def AgeTestModel.sparsePullback {db du dd : Nat}
    (V : AgeTestModel db du dd) (N : Nat)
    (real : Nat → Prop) (e : Nat → Nat) :
    AgeTestModel db du dd where
  carrier := {x | x < N ∧ real x}
  binary := fun x y t => V.binary (e x) (e y) t
  unary := fun x t => V.unary (e x) t
  diagonal := fun x t => V.diagonal (e x) t

/-- The chosen source indices are mapped inducedly to the target
whenever e is strictly increasing on the selected real positions. -/
def AgeTestModel.sparsePullback_induced
    {db du dd : Nat}
    (V : AgeTestModel db du dd) (N : Nat)
    (real : Nat → Prop) (e : Nat → Nat)
    (hOrder : ∀ x y, x < N → y < N → real x → real y →
      x < y → e x < e y)
    (hInside : ∀ x, x < N → real x → e x ∈ V.carrier) :
    (V.sparsePullback N real e).InducedEmbeddingOnCarrier V where
  toFun := e
  order := by
    intro x y hx hy hxy
    exact hOrder x y hx.1 hy.1 hx.2 hy.2 hxy
  inside := by
    intro x hx
    exact hInside x hx.1 hx.2
  binary := by
    intro x y hx hy hne t
    rfl
  unary := by
    intro x hx t
    rfl
  diagonal := by
    intro x hx t
    rfl

/-- Every selected L atom can be pulled back and the empty numerical
slots filled by neutral vertices, without introducing forbidden
configurations. This is the finite source-age step needed by M2. -/
theorem AgeTestModel.sparsePullback_fill_avoids
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (V : AgeTestModel db du dd)
    (N : Nat) (real : Nat → Prop) (e : Nat → Nat)
    (hOrder : ∀ x y, x < N → y < N → real x → real y →
      x < y → e x < e y)
    (hInside : ∀ x, x < N → real x → e x ∈ V.carrier)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids V) :
    ∀ bad, bad ∈ family →
      bad.Avoids ((V.sparsePullback N real e).fillNeutralCarrier N) := by
  have hSparse : ∀ bad, bad ∈ family →
      bad.Avoids (V.sparsePullback N real e) :=
    (V.sparsePullback_induced N real e hOrder hInside).preserves_avoidance
      family hAvoid
  intro bad hBad
  exact bad.avoids_fillNeutralCarrier
    (V.sparsePullback N real e) N (by
      intro x hx
      exact hx.1)
    (hSparse bad hBad)

end SuccessorTree.V10
