import SuccessorTree.V10.CanonicalStepRealization
import Mathlib.Tactic

/-!
# S3 decomposition of every admissible Kpt cover

The Kpt family consists of complete types at free E cuts from
forbidden-free partial structures. A cover a ⋖ b therefore comes
from a witness A, v for b. At the new level ell, this witness
canonically gives the predecessor, an empty-or-positive-singleton
parameter, and the terminal Sigma letter.

The realization theorem constructs a cover a' ⋖ b' with exactly
the same raw target b'=b. Since both a and a' are immediate
predecessors of the same node in a forest, they are equal.

Thus EVERY cover admits an exact canonical successor-graph
decomposition. This is S3 for the step graph; the forward function
and restriction of the temporary raw letter alphabet to the
admissible Sigma family still require separate proofs.
-/

namespace SuccessorTree.V10

/-- Every admissible cover has a canonical complete predecessor,
empty-or-positive-singleton parameter and terminal L+ letter.
This is S3 for the graph of the concrete successor operation. -/
theorem canonicalKptStep_exists_of_covBy
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b : AdmissibleKptNode family}
    (hab : a ⋖ b) :
    ∃ (p : List (AdmissibleKptNode family))
      (c : RawKptLetter db du dd),
      IsCanonicalKptStep family a p c b := by
  let ell := a.1.1
  have hbLevel : b.1.1 = ell + 1 := by
    exact admissibleKpt_covBy_level hab
  obtain ⟨A, v, hv, hAvoid, hRawNode⟩ := b.2
  have hFree : A.freeLevel v = ell + 1 := by
    have h := congrArg Sigma.fst hRawNode
    change b.1.1 = A.freeLevel v at h
    omega
  obtain ⟨a', b', p, c, hStep, hCover, hb'⟩ :=
    exists_canonical_step_from_ambient family A v ell hv hAvoid hFree
  have hbWitness : b.1 =
      (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
        RawPartialTypeNode db du dd) := by
    rw [hRawNode]
    change
      (⟨A.freeLevel v,
        A.partialTypeAt (A.freeLevel v) v⟩ :
          RawPartialTypeNode db du dd) =
      (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
        RawPartialTypeNode db du dd)
    rw [hFree]
  have hbeq : b' = b :=
    Subtype.ext (hb'.trans hbWitness.symm)
  have haLevel : LevelTree.lev a' = LevelTree.lev a := by
    have h1 := LevelTree.covBy_level_eq hCover
    have h2 := LevelTree.covBy_level_eq hab
    rw [hbeq] at h1
    omega
  have haeq : a' = a := by
    have hA : a' ≤ b := by simpa only [hbeq] using hCover.le
    rcases LevelTree.comparable_below hA hab.le with h | h
    · exact LevelTree.same_level_of_le h haLevel
    · exact (LevelTree.same_level_of_le h haLevel.symm).symm
  subst a'
  subst b'
  exact ⟨p, c, hStep⟩

end SuccessorTree.V10
