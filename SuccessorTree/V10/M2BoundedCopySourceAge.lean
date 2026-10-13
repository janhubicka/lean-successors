import SuccessorTree.V10.M2SparsePullbackAge
import Mathlib.Tactic

/-!
# Explicit bounded forbidden-copy pullback for the M2 insertion age test

If a forbidden r-vertex pattern occurs in a finite target age witness,
its vertices are enumerated in increasing order by an injective map
e : Fin r → Nat. The initial n source coordinates are sent by the
strictly increasing level map lambda to retained target positions
below the missing coordinate m. The other r numerical source slots
represent precisely those e(a)>m; every unused slot is a neutral filler.

This avoids a separate order enumeration of a possibly sparse finite
carrier. A strictly increasing map is required only on the genuinely
selected source positions, and hence the carrier-relative embedding
and neutral completion from M2SparsePullbackAge apply directly.
-/

namespace SuccessorTree.V10

/-- Selected source positions: the old initial n coordinates and the
slots corresponding to upper vertices of the alleged forbidden copy. -/
def boundedCopyReal (n m r : Nat) (e : Fin r → Nat) (x : Nat) : Prop :=
  x < n ∨ ∃ a : Fin r, x = n + a.val ∧ m < e a

/-- The source-to-target address: retained levels below n, and
the forbidden copy's own increasing enumeration above n. -/
noncomputable def boundedCopyAddress
    (lambda : Nat → Nat) (n r : Nat) (e : Fin r → Nat) (x : Nat) : Nat :=
  if hx : x < n then lambda x
  else if h : x - n < r then e ⟨x - n,h⟩ else 0

@[simp] theorem boundedCopyAddress_low
    (lambda : Nat → Nat) (n r : Nat) (e : Fin r → Nat)
    (x : Nat) (hx : x < n) :
    boundedCopyAddress lambda n r e x = lambda x := by
  simp [boundedCopyAddress,hx]

@[simp] theorem boundedCopyAddress_upper
    (lambda : Nat → Nat) (n r : Nat) (e : Fin r → Nat)
    (a : Fin r) :
    boundedCopyAddress lambda n r e (n + a.val) = e a := by
  have hNot : ¬ n + a.val < n := by omega
  have hFin : (n + a.val) - n < r := by omega
  simp [boundedCopyAddress,hNot,hFin]

/-- The piecewise address map is STRICTLY ordered on the real carrier.
No inequality is asserted at dummy positions: their target values are
irrelevant and can even collide with genuine target coordinates. -/
theorem boundedCopyAddress_order
    (lambda : Nat → Nat) (hLambda : StrictMono lambda)
    (n m r : Nat) (e : Fin r → Nat) (hE : StrictMono e)
    (hBelow : ∀ i, i < n → lambda i < m)
    (x y : Nat)
    (hx : boundedCopyReal n m r e x)
    (hy : boundedCopyReal n m r e y)
    (hxy : x < y) :
    boundedCopyAddress lambda n r e x <
      boundedCopyAddress lambda n r e y := by
  rcases hx with hxLow | ⟨a,haAddr,haUpper⟩
  · rcases hy with hyLow | ⟨b,hbAddr,hbUpper⟩
    · simpa [boundedCopyAddress_low lambda n r e x hxLow,
        boundedCopyAddress_low lambda n r e y hyLow]
        using hLambda hxy
    · subst y
      rw [boundedCopyAddress_low lambda n r e x hxLow,
        boundedCopyAddress_upper lambda n r e b]
      exact lt_trans (hBelow x hxLow) hbUpper
  · rcases hy with hyLow | ⟨b,hbAddr,hbUpper⟩
    · omega
    · subst x
      subst y
      rw [boundedCopyAddress_upper lambda n r e a,
        boundedCopyAddress_upper lambda n r e b]
      apply hE
      omega

/-- The piecewise real carrier maps into the target whenever all
retained initial positions and selected upper copies do. -/
theorem boundedCopyAddress_inside {db du dd : Nat}
    (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (hLow : ∀ i, i < n → lambda i ∈ V.carrier)
    (hUpper : ∀ a : Fin r, m < e a → e a ∈ V.carrier)
    (x : Nat) (hx : boundedCopyReal n m r e x) :
    boundedCopyAddress lambda n r e x ∈ V.carrier := by
  rcases hx with hxLow | ⟨a,haAddr,haUpper⟩
  · rw [boundedCopyAddress_low lambda n r e x hxLow]
    exact hLow x hxLow
  · subst x
    rw [boundedCopyAddress_upper lambda n r e a]
    exact hUpper a haUpper

/-- Dense source L model formed by pulling back only selected target
vertices and inserting neutral non-edges at unused upper slots. -/
noncomputable def boundedCopySourceAge {db du dd : Nat}
    (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat) :
    AgeTestModel db du dd :=
  ((V.sparsePullback (n+r) (boundedCopyReal n m r e)
      (boundedCopyAddress lambda n r e)).fillNeutralCarrier (n+r))

/-- The bounded copy source L model is forbidden-free whenever the
target L model is forbidden-free. Upper vertices are taken from the
given strictly increasing forbidden-pattern enumeration, with no
unjustified E-expansion or age-preservation assumption on F. -/
theorem boundedCopySourceAge_avoids {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (V : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m r : Nat) (e : Fin r → Nat)
    (hLambda : StrictMono lambda) (hE : StrictMono e)
    (hBelow : ∀ i, i < n → lambda i < m)
    (hLowInside : ∀ i, i < n → lambda i ∈ V.carrier)
    (hUpperInside : ∀ a : Fin r, m < e a → e a ∈ V.carrier)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids V) :
    ∀ bad, bad ∈ family →
      bad.Avoids (boundedCopySourceAge V lambda n m r e) := by
  change ∀ bad, bad ∈ family →
    bad.Avoids
      ((V.sparsePullback (n+r) (boundedCopyReal n m r e)
        (boundedCopyAddress lambda n r e)).fillNeutralCarrier (n+r))
  apply V.sparsePullback_fill_avoids family (n+r)
    (boundedCopyReal n m r e) (boundedCopyAddress lambda n r e)
  · intro x y hxN hyN hxReal hyReal hxy
    exact boundedCopyAddress_order lambda hLambda n m r e hE
      hBelow x y hxReal hyReal hxy
  · intro x hxN hxReal
    exact boundedCopyAddress_inside V lambda n m r e
      hLowInside hUpperInside x hxReal
  · exact hAvoid

end SuccessorTree.V10
