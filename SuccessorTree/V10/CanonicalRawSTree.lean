import SuccessorTree.V10.CanonicalStepUniqueness
import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# The canonical successor graph as an actual S-tree operation

We define the forward Option-valued successor by the graph of exact
one-step partial-type extensions: a prescribed predecessor, a
canonical empty-or-positive-singleton parameter, a terminal
two-vertex L+ letter, and the E-cut/no-new-tuples constraints.

The graph is functional, has S2-unique input decompositions,
every defined successor is an immediate cover with strictly lower
parameter levels (S1), and every admissible cover is represented
(S3). Classical choice merely selects a witness from the PROVED
unique-output graph; it is not an extra mathematical axiom.

This establishes an S-tree on the normalized forbidden-free Kpt
forest with an alphabet of ALL raw level-one L+ types. The
published alphabet Sigma is the smaller subset of ADMISSIBLE
level-one types. Its restriction requires a separate age-preserving
two-vertex-letter realization and cannot be inferred from this
broader STree alone.

The monoid M and M1--M3 remain unformalized for the concrete tree.
-/

namespace SuccessorTree.V10

/-- Exact forward successor defined by the canonical one-step graph.
The output is unique whenever the relation is nonempty. -/
noncomputable def canonicalKptSucc
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : RawKptLetter db du dd) :
    Option (AdmissibleKptNode family) := by
  classical
  exact if h : ∃ b : AdmissibleKptNode family,
      IsCanonicalKptStep family a p c b then
    some (Classical.choose h)
  else none

/-- Every output of the chosen function actually lies in the
canonical graph; no random cover may be selected. -/
theorem canonicalKptSucc_spec
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (h : canonicalKptSucc family a p c = some b) :
    IsCanonicalKptStep family a p c b := by
  classical
  by_cases hex : ∃ x : AdmissibleKptNode family,
      IsCanonicalKptStep family a p c x
  · have hh : some (Classical.choose hex) = some b := by
      simpa [canonicalKptSucc, hex] using h
    have hb : Classical.choose hex = b := Option.some.inj hh
    simpa [hb] using (Classical.choose_spec hex)
  · simp [canonicalKptSucc, hex] at h

/-- A witness to the canonical step graph is automatically the
output of the forward successor: uniqueness of target is proved,
not assumed. -/
theorem canonicalKptSucc_eq_some_of_step
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) :
    canonicalKptSucc family a p c = some b := by
  classical
  have hex : ∃ x : AdmissibleKptNode family,
      IsCanonicalKptStep family a p c x := ⟨b, hStep⟩
  have hChoice : IsCanonicalKptStep family a p c
      (Classical.choose hex) := Classical.choose_spec hex
  have heq : Classical.choose hex = b :=
    canonicalKptStep_target_unique family hChoice hStep
  unfold canonicalKptSucc
  rw [dif_pos hex]
  exact congrArg Option.some heq

/-- For the raw two-vertex alphabet, all three S-tree axioms follow
from the concrete normalized Kpt witness construction and uniqueness.
No S1, S2 or S3 axiom is added to the model. -/
noncomputable def canonicalKptRawSTree
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    SuccessorTree.STree (AdmissibleKptNode family)
      (RawKptLetter db du dd) where
  succ := canonicalKptSucc family
  s1 := by
    intro a p c b h
    have hStep := canonicalKptSucc_spec family h
    exact ⟨canonicalKptStep_covBy family hStep,
      fun x hx => canonicalKptStep_parameter_lt family hStep x hx⟩
  s2 := by
    intro a b x p q c d ha hb
    exact canonicalKptStep_inputs_unique family
      (canonicalKptSucc_spec family ha)
      (canonicalKptSucc_spec family hb)
  s3 := by
    intro a b hab
    obtain ⟨p, c, hStep⟩ :=
      canonicalKptStep_exists_of_covBy family hab
    exact ⟨p, c, canonicalKptSucc_eq_some_of_step family hStep⟩

/-- The exact S-tree successor uses the constructed canonical
partial-type successor graph. -/
theorem canonicalKptRawSTree_succ_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : RawKptLetter db du dd) :
    (canonicalKptRawSTree family).succ a p c =
      canonicalKptSucc family a p c := rfl

end SuccessorTree.V10
