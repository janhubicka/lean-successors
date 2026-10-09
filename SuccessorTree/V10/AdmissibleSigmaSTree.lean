import SuccessorTree.V10.TerminalLetterAge
import SuccessorTree.V10.CanonicalRawSTree
import Mathlib.Tactic

/-!
# The canonical Kpt S-tree with the *admissible* Sigma alphabet

The previous canonical STree had the correct Kpt vertex set and
one-step successor graph, but its letters were arbitrary raw
two-vertex L+ types. For an exact match with Definition 6.30,
the alphabet Sigma must consist of admissible level-one Kpt nodes.

The terminal-letter replica proves that EVERY canonical successor
has a letter in this smaller alphabet. We therefore restrict the
verified Option-valued successor to this alphabet and transfer S1
and S2 directly. S3 uses the admissibility of the extracted
terminal letter.

This is the entire S1--S3 claim of Proposition 6.32 in the
normalized Boolean-vector presentation, provided the preceding
specific witness/age lemmas all compile and their exact-head
transitive-axiom audit is green. It does not identify arbitrary
nullary symbols or the split diagonal encoding with the paper's
literal L, nor verify the concrete monoid M1--M3.
-/

namespace SuccessorTree.V10

/-- The alphabet of level-one admissible partial types, exactly
as in the manuscript (but with explicit normalized binary coding). -/
abbrev AdmissibleKptSigma
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :=
  {c : RawKptLetter db du dd //
    IsAdmissibleRawType family
      (⟨1,c⟩ : RawPartialTypeNode db du dd)}

/-- Every letter produced by the canonical Kpt successor graph is
an admissible one-level partial type. This uses an actual forbidden-
free partial-structure witness for the last two-vertex L+ letter. -/
theorem canonicalKptStep_letter_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) :
    IsAdmissibleRawType family
      (⟨1,c⟩ : RawPartialTypeNode db du dd) := by
  obtain ⟨ell, f, hf, Q, hBase, hTarget, hLetter,
    hValid, hParam, hGate⟩ := hStep
  obtain ⟨A, v, hv, hAvoid, hNode⟩ := b.2
  have hSource :
      (⟨ell + 1, Q⟩ : RawPartialTypeNode db du dd) =
        A.rawTypeAtFree v :=
    hTarget.symm.trans hNode
  have hFree : A.freeLevel v = ell + 1 := by
    have h := congrArg Sigma.fst hSource
    change ell + 1 = A.freeLevel v at h
    omega
  have hQ : Q = A.partialTypeAt (ell + 1) v := by
    have hRaw :
        (⟨ell + 1,Q⟩ : RawPartialTypeNode db du dd) =
        (⟨ell + 1,A.partialTypeAt (ell + 1) v⟩ :
          RawPartialTypeNode db du dd) := by
      rw [hSource]
      change
        (⟨A.freeLevel v,
          A.partialTypeAt (A.freeLevel v) v⟩ :
          RawPartialTypeNode db du dd) =
        (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
          RawPartialTypeNode db du dd)
      rw [hFree]
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      using hRaw
  rw [hLetter, hQ]
  exact terminalLetter_is_admissible family A v ell hv hAvoid
    (by omega)

/-- Restrict the genuine canonical successor to the admissible
Sigma alphabet, rather than changing the tree or its parameters. -/
noncomputable def admissibleKptSucc
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family) :
    Option (AdmissibleKptNode family) :=
  canonicalKptSucc family a p c.1

/-- The literal normalized Kpt class and its *admissible*
Sigma alphabet form an S-tree under the reconstructed
no-new-tuples successor operation. -/
noncomputable def admissibleKptSTree
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    SuccessorTree.STree (AdmissibleKptNode family)
      (AdmissibleKptSigma family) where
  succ := admissibleKptSucc family
  s1 := by
    intro a p c b h
    exact (canonicalKptRawSTree family).s1 h
  s2 := by
    intro a b x p q c d ha hb
    have h := (canonicalKptRawSTree family).s2 ha hb
    exact ⟨h.1,h.2.1,Subtype.ext h.2.2⟩
  s3 := by
    intro a b hab
    obtain ⟨p,c,hStep⟩ :=
      canonicalKptStep_exists_of_covBy family hab
    have hAdmissible :=
      canonicalKptStep_letter_admissible family hStep
    exact ⟨p,⟨c,hAdmissible⟩,
      canonicalKptSucc_eq_some_of_step family hStep⟩

/-- The S-tree's successor is exactly the same canonical graph as
before; admissibility restricts labels but does not add tuples. -/
theorem admissibleKptSTree_succ_eq
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (a : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family) :
    (admissibleKptSTree family).succ a p c =
      canonicalKptSucc family a p c.1 := rfl

end SuccessorTree.V10
