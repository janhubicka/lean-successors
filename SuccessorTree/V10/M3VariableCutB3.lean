import SuccessorTree.V10.M3CanonicalCloneInitial
import Mathlib.Tactic

/-!
# Corrected finite M3 B3 with a source-dependent earlier free cut

In an M3 duplicate, the copied ordinary vertex n is fixed, but its
canonical free cut d can depend on the ambient lower socle S0.
Different compatibility classes of prescribed source types need not
have the same d. The earlier fixed-cut reduction is therefore stronger
than necessary and should not be used as an M3 hypothesis.

For each S0, obtain its own cut d and exact middle-clone ordinary L
column. The upper terminal-pair clone condition is uniform. For each
finite L-age witness W, the same d applies to its common initial L
socle, and the finite irreducible projection proves corrected B3.
No auxiliary E structure occurs on W and no common d across S0 is
required.
-/

namespace SuccessorTree.V10

/-- The finite corrected-B3 consequence needed in M3 permits the
ordinary source n's free cut to depend on S0. This is a genuinely weaker
input than a globally fixed cut and is stable under compatibility
classes. Every L-age witness is checked without any E assumption. -/
theorem PrescribedBoringData.correctedB3_of_middle_clone_varying_cut
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) (hn : n < ell)
    (hLower : ∀ S0, S0 ∈ F.source →
      ∃ d : Nat,
        MiddleCloneInitialL
          (prescribedOrdinarySocle (F.target S0)) n ell d)
    (hUpper : F.MiddleCloneUpperL n hn) :
    F.CorrectedB3 family := by
  intro S0 hS0
  obtain ⟨d, hClone⟩ := hLower S0 hS0
  intro W hFinite hSame hPrescribed hDeletion
  have hData : MiddleCloneLData W n ell d :=
    F.middleCloneLData_of_age_witness n d hn
      (prescribedOrdinarySocle (F.target S0)) W
      hClone hUpper hSame hPrescribed
  exact hData.avoidance_of_deletion family hDeletion

end SuccessorTree.V10
