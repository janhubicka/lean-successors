import SuccessorTree.V10.LevelRemovalAdmissiblePrefix
import SuccessorTree.V10.RawPrefixOrder
import Mathlib.Tactic

/-!
# Admissibility of an intrinsically deleted lower type from an upper witness

The future uniform M2 deletion map must be defined from the
complete record of F(a), not from a chosen source successor.
The witness of an upper Kpt type is used only to prove that this
already specified shorter record is admissible.

The local structural input is the checked finite guarded deletion
and its admissible-prefix theorem. Complete raw prefix equality
recovers the exact full L+ lower record from any upper witness.
No uniform deletion map, M2 or corrected-B3 necessity is assumed.
-/

namespace SuccessorTree.V10

/-- If lower is a complete Kpt prefix of upper, a finite
forbidden-free witness of upper with the sharp guard at m certifies
admissibility of the intrinsic deletion of m from lower.

The resulting raw node depends ONLY on lower and m; the selected
upper witness enters solely into the proof of admissibility.
This is the value-level independence needed at the M2 boundary. -/
theorem admissible_deleted_lower_of_guarded_upper
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (lower upper : AdmissibleKptNode family)
    (hLower : lower ≤ upper)
    (m : Nat) (hm : m < lower.1.1)
    (A : EnumeratedPartialStructure db du dd)
    (v : Nat) (hv : v < A.size)
    (hRaw : upper.1 = A.rawTypeAtFree v)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hNext : m + 1 < A.size)
    (hGuard : A.freeLevel (m + 1) < m) :
    IsAdmissibleRawType family
      (⟨lower.1.1 - 1,
        lower.1.2.deleteOrdinary m hm⟩ :
          RawPartialTypeNode db du dd) := by
  have hPrefix : lower.1 ≤ upper.1 := hLower
  obtain ⟨hCut, hRecord⟩ := hPrefix
  have hFree : upper.1.1 = A.freeLevel v := by
    have hh := congrArg Sigma.fst hRaw
    change upper.1.1 = A.freeLevel v at hh
    exact hh
  have hUpperRecord :
      upper.1.2 = A.partialTypeAt upper.1.1 v := by
    have hSigma :
        (⟨upper.1.1,upper.1.2⟩ : RawPartialTypeNode db du dd) =
          (⟨upper.1.1,A.partialTypeAt upper.1.1 v⟩ :
            RawPartialTypeNode db du dd) := by
      calc
        (⟨upper.1.1,upper.1.2⟩ : RawPartialTypeNode db du dd) =
            A.rawTypeAtFree v := hRaw
        _ = (⟨upper.1.1,A.partialTypeAt upper.1.1 v⟩ :
            RawPartialTypeNode db du dd) := by
          change
            (⟨A.freeLevel v,
              A.partialTypeAt (A.freeLevel v) v⟩ :
                RawPartialTypeNode db du dd) = _
          rw [←hFree]
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hSigma
  have hLowerRecord :
      lower.1.2 = A.partialTypeAt lower.1.1 v := by
    calc
      lower.1.2 = upper.1.2.restrict hCut := hRecord
      _ = (A.partialTypeAt upper.1.1 v).restrict hCut := by
        rw [hUpperRecord]
      _ = A.partialTypeAt lower.1.1 v :=
        A.partialTypeAt_restrict
          lower.1.1 upper.1.1 v hCut
  have hCutA : lower.1.1 ≤ A.freeLevel v := by omega
  have hAd := admissible_deleted_type_at_shorter_cut
    family A m lower.1.1 v hNext hGuard hv hCutA hm hAvoid
  rw [hLowerRecord]
  exact hAd

end SuccessorTree.V10
