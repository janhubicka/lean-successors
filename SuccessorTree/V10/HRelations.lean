import SuccessorTree.V10.SocleE
import SuccessorTree.V10.FirstDisagreement
import Mathlib.Tactic

/-!
# Exact finite binary-relation copying in the H construction

This is a proposed precise interpretation of the manuscript's one-way
"two-vertex restriction is a substructure of K" condition. It specifies
exactly which binary relation bits are copied; both directed orientations
of each binary symbol can be included in the finite relation vector.

Unary and diagonal relation bits must be copied from each real vertex's
base singleton, and fake vertices receive the chosen neutral singleton.
Those singleton data do not affect the crossing trace, but must be included
in the full partial-type representation. E is generated independently
in SocleE, and is not part of the L-reduct.
-/

namespace SuccessorTree.V10

/-- The gate on a pair of real H vertices in different base blocks. -/
def admissibleRealPair (k i j q m : Nat) : Prop :=
  i < j ∧ q ≤ k ∧ m ≤ k ∧ (q < m ∨ (q = m ∧ m = k))

/-- Exactly copy binary relation bits on admissible real pairs and put no
binary relation on any other ordered pair of real blocks. -/
def copiedRealPair {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat) : Fin d → Bool :=
  fun r => if i < j ∧ q ≤ k ∧ m ≤ k ∧
      (q < m ∨ (q = m ∧ m = k)) then B i j r else false

/-- Admissible pairs have exactly the corresponding base tuple. -/
theorem copiedRealPair_eq_of_admissible
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat)
    (h : admissibleRealPair k i j q m) :
    copiedRealPair B k i j q m = B i j := by
  funext r
  simpa [copiedRealPair, admissibleRealPair] using
    (if_pos h : (if admissibleRealPair k i j q m then B i j r else false) = B i j r)

/-- All forbidden real pairs carry the empty binary tuple. -/
theorem copiedRealPair_empty_of_not_admissible
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat)
    (h : ¬ admissibleRealPair k i j q m) :
    copiedRealPair B k i j q m = emptyBinaryPattern d := by
  funext r
  simpa [copiedRealPair, admissibleRealPair, emptyBinaryPattern] using
    (if_neg h : (if admissibleRealPair k i j q m then B i j r else false) = false)

/-- A nonempty copied tuple forces the ordered pair and generation gate. -/
theorem copiedRealPair_nonempty_implies_admissible
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat)
    (hne : copiedRealPair B k i j q m ≠ emptyBinaryPattern d) :
    admissibleRealPair k i j q m := by
  by_contra hnot
  exact hne (copiedRealPair_empty_of_not_admissible B k i j q m hnot)

/-- The third partial-structure axiom: any irreducible copied L-pair
lies in the downward-generated auxiliary E relation. -/
theorem nonemptyCopiedPair_generatesE
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat)
    (hne : copiedRealPair B k i j q m ≠ emptyBinaryPattern d) :
    generatedE k j m (hPosition k i q) := by
  obtain ⟨hij, hqk, _, hgate⟩ :=
    copiedRealPair_nonempty_implies_admissible B k i j q m hne
  exact generatedE_of_allowedPair k i j q m hij hqk hgate

/-- Two different generations in one base block have no intervertex
L-relations; this is the first-index injectivity needed for
irreducible forbidden structures in the signature argument. -/
theorem sameBlock_no_binary
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i q m : Nat) :
    copiedRealPair B k i i q m = emptyBinaryPattern d := by
  apply copiedRealPair_empty_of_not_admissible
  simp [admissibleRealPair]

/-- The exact copied L-relation is the same finite directed-binary trace
already classified in FirstDisagreement, whenever i<j and both
generations belong to the H block range. -/
theorem copiedRealPair_matches_trace
    {d : Nat} (B : Nat → Nat → Fin d → Bool)
    (k i j q m : Nat)
    (hij : i < j) (hq : q ≤ k) (hm : m ≤ k) :
    copiedRealPair B k i j q m =
      bundledTrace B k j m i q := by
  funext r
  by_cases hgate : q < m ∨ (q = m ∧ m = k)
  · simp [copiedRealPair, bundledTrace, traceBit, hij, hq, hm, hgate]
  · simp [copiedRealPair, bundledTrace, traceBit, hij, hq, hm, hgate]

end SuccessorTree.V10
