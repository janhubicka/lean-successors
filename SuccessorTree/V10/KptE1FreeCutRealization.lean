import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# Concrete E free-cut realization for finite partial structures

A finite enumerated L-model A and an explicitly specified free-cut
profile f determine a Boolean E relation by

    E(u,v) := (v < N and u < f(v)).

If each positive profile value satisfies f(v)<v, this E is spaced
and downward-closed with the exact first missing E coordinate f(v).
If each actual linked L-pair (u,v) has u<f(v), the resulting finite
L+ partial structure satisfies ALL axioms of Definition 6.28.

This is an actual constructor of EnumeratedPartialStructure; no
unjustified E expansion is attached to any forbidden-family L-age
test witness. This general lemma will be used only AFTER a legitimate
finite L structure with inherited forbidden-free age has been
constructed, so no age assumption is inserted or changed here.

For the concrete Kpt E1 pullback, the intended profile consists
of the already valid source old cuts, the parameter cut f<n at the
new ordinary vertex n, cut 0 at the neutral spacer n+1 and cut
n+1 at the terminal type witness n+2.
-/

namespace SuccessorTree.V10

/-- A Boolean E column with a prescribed first missing coordinate. -/
def finiteFreeCutE
    (N : Nat) (f : Nat → Nat) (u v : Nat) : Bool :=
  decide (v < N ∧ u < f v)

/-- Exact incidence in the prescribed column, including negative bits. -/
theorem finiteFreeCutE_true_iff
    (N : Nat) (f : Nat → Nat) (u v : Nat) :
    finiteFreeCutE N f u v = true ↔ v < N ∧ u < f v := by
  simp [finiteFreeCutE]

theorem finiteFreeCutE_false_at_cut
    (N : Nat) (f : Nat → Nat) (v : Nat) :
    finiteFreeCutE N f (f v) v = false := by
  simp [finiteFreeCutE]

/-- Strict spacing follows from the local condition that every
NONEMPTY E-column has its first free cut strictly below v.
Columns of cut zero impose no spacing requirement. -/
theorem finiteFreeCutE_spaced
    (N : Nat) (f : Nat → Nat)
    (hCuts : ∀ v, v < N → f v = 0 ∨ f v < v) :
    SpacedE (finiteFreeCutE N f) := by
  intro u v h
  have hv := (finiteFreeCutE_true_iff N f u v).mp h
  rcases hCuts v hv.1 with hf0 | hfv
  · omega
  · omega

/-- Prefix columns are downward closed without any extra condition
on the values of the cut profile. -/
theorem finiteFreeCutE_downward
    (N : Nat) (f : Nat → Nat) :
    DownwardE (finiteFreeCutE N f) := by
  intro u v h w hw
  have hv := (finiteFreeCutE_true_iff N f u v).mp h
  exact (finiteFreeCutE_true_iff N f w v).mpr
    ⟨hv.1, lt_trans hw hv.2⟩

/-- Each E endpoint lies inside the finite carrier. -/
theorem finiteFreeCutE_inside
    (N : Nat) (f : Nat → Nat)
    (hCuts : ∀ v, v < N → f v = 0 ∨ f v < v)
    (u v : Nat)
    (h : finiteFreeCutE N f u v = true) :
    u < N ∧ v < N := by
  have hv := (finiteFreeCutE_true_iff N f u v).mp h
  rcases hCuts v hv.1 with hf0 | hfv
  · omega
  · omega

/-- Exact first E gap at every carrier vertex. -/
theorem finiteFreeCutE_isFreeCut
    (N : Nat) (f : Nat → Nat) (v : Nat) (hv : v < N) :
    IsFreeCut (finiteFreeCutE N f) v (f v) := by
  constructor
  · intro u hu
    exact (finiteFreeCutE_true_iff N f u v).mpr ⟨hv,hu⟩
  · exact finiteFreeCutE_false_at_cut N f v

/-- The canonical free level of the ACTUAL constructed E really is
the specified profile value, not an arbitrary equivalent cut. -/
theorem finiteFreeCutE_canonicalFreeLevel
    (N : Nat) (f : Nat → Nat)
    (hCuts : ∀ v, v < N → f v = 0 ∨ f v < v)
    (v : Nat) (hv : v < N) :
    canonicalFreeLevel (finiteFreeCutE N f)
      (finiteFreeCutE_spaced N f hCuts)
      (finiteFreeCutE_downward N f) v = f v := by
  apply freeCut_unique (finiteFreeCutE N f) v
  · exact canonicalFreeLevel_isFreeCut
      (finiteFreeCutE N f)
      (finiteFreeCutE_spaced N f hCuts)
      (finiteFreeCutE_downward N f) v
  · exact finiteFreeCutE_isFreeCut N f v hv

/-- A genuine finite L+ partial structure from an existing finite
L age-test model and a specified free-cut profile. Every E axiom
is proved and the L reduct is UNCHANGED.

The age of A itself is not assumed: the caller must separately
provide forbidden-free L age before claiming a Kpt node is admissible.
The linked-pair premise is explicit and precisely scoped. -/
def EnumeratedPartialStructure.ofFreeCutProfile
    {db du dd : Nat}
    (N : Nat)
    (A : AgeTestModel db du dd)
    (hCarrier : ∀ v, v ∈ A.carrier ↔ v < N)
    (f : Nat → Nat)
    (hCuts : ∀ v, v < N → f v = 0 ∨ f v < v)
    (hLinked : ∀ u v, u < v → u < N → v < N →
      (∃ r : Fin db,
        A.binary u v r = true ∨ A.binary v u r = true) →
      u < f v) :
    EnumeratedPartialStructure db du dd where
  size := N
  L := A
  carrier_iff := hCarrier
  E := finiteFreeCutE N f
  E_inside := finiteFreeCutE_inside N f hCuts
  spaced := finiteFreeCutE_spaced N f hCuts
  downward := finiteFreeCutE_downward N f
  linked_E := by
    intro u v huv hu hv hLink
    exact (finiteFreeCutE_true_iff N f u v).mpr
      ⟨hv,hLinked u v huv hu hv hLink⟩

end SuccessorTree.V10
