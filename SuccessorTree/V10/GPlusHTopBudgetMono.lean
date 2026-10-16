import SuccessorTree.V10.GPlusFinitePaletteCoverageMono
import SuccessorTree.V10.HUniformEnvelopeBound
import Mathlib.Tactic

/-!
# Uniform numerical HTop envelope height is monotone in the tuple size

The genuine finite H+ envelope bound depends on the cardinality of the
chosen top-generation seed block set, whereas a universal big-Ramsey
bound must depend only on the size q of the finite source A.

The exact recurrence b(q) is monotone: its signature-capacity
polynomial R is monotone, so a simple induction shows the descending
cumulative generation budget M(q) is monotone in q. Consequently
the *actual* sharp H+ level bound B(q) is monotone.

These are elementary numerical lemmas: no alteration to Algorithm 5.4,
the finite Kpt representation palette, or the existing manuscript
recurrence is made. In particular this is NOT a hypothetical uniform
envelope lemma: it is a comparison of the exact verified b(q).
-/

namespace SuccessorTree.V10

/-- The exact descending recurrence is monotone in its initial
number of top-generation original coordinates, provided R is
monotone. All generation indices are allowed, including zero. -/
theorem descendingCumulativeBudget_mono_initial
    (R : Nat → Nat) (hR : Monotone R)
    {q Q : Nat} (hqQ : q ≤ Q) (j : Nat) :
    descendingCumulativeBudget R q j ≤
      descendingCumulativeBudget R Q j := by
  induction j with
  | zero =>
      simp only [descendingCumulativeBudget]
      omega
  | succ j ih =>
      have hRmon := hR ih
      change
        2 * descendingCumulativeBudget R q j +
            R (descendingCumulativeBudget R q j) ≤
          2 * descendingCumulativeBudget R Q j +
            R (descendingCumulativeBudget R Q j)
      omega

/-- The exact manuscript upper bound b(q)=2(q+1+M(q))+R(M(q))+1,
using the verified descending cumulative generation recurrence.
No new numerical overestimate is introduced. -/
def numericHTopUniformPaletteHeight
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (k q : Nat) : Nat :=
  let sizes : Fin family.length → Nat :=
    fun i => (family.get i).patternCard
  let R : Nat → Nat := ageSignatureCapacity sizes
  let M := descendingCumulativeBudget R q (k-1)
  2*(q+1+M)+R M+1

/-- The single finite HTop palette height required for every
q-point pattern increases monotonically when the tuple size
increases. The full exact recurrence is preserved. -/
theorem numericHTopUniformPaletteHeight_mono_q
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (k : Nat) {q Q : Nat} (h : q ≤ Q) :
    numericHTopUniformPaletteHeight family k q ≤
      numericHTopUniformPaletteHeight family k Q := by
  let sizes : Fin family.length → Nat :=
    fun i => (family.get i).patternCard
  let R : Nat → Nat := ageSignatureCapacity sizes
  let Mq : Nat := descendingCumulativeBudget R q (k-1)
  let MQ : Nat := descendingCumulativeBudget R Q (k-1)
  have hM : Mq ≤ MQ :=
    descendingCumulativeBudget_mono_initial R
      (ageSignatureCapacity_mono sizes) h (k-1)
  have hCap : R Mq ≤ R MQ :=
    (ageSignatureCapacity_mono sizes) hM
  change 2*(q+1+Mq)+R Mq+1 ≤
    2*(Q+1+MQ)+R MQ+1
  omega

end SuccessorTree.V10
