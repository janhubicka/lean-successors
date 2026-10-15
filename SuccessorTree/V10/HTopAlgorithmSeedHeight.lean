import SuccessorTree.V10.HTopGenerationSeeds
import SuccessorTree.EnvelopeAlgorithm
import Mathlib.Tactic

/-!
# V10 Algorithm 5.4: actual numerical HTop seed-height bound

The genuine numericHTopGenerationSeeds are exactly one actual original
root U=(finiteNumericH ...).kptOriginal c together with selected
ancestors of U at top-generation coordinates hPosition k i k.

The numerical root level is the literal free E cut ell=freeLevel(c).
All selected ancestors have level <=ell by the EXISTING hWithin
proof supplied to the finite constructor. Thus the entire genuine
finite Kpt seed family lies below ell, which is precisely the
initial-height hypothesis of AlgorithmRun.fullInvariant.

No additional envelope, E1 or representation assumption is required
for this purely geometric height bound. It is kept separate from the
E1-dependent output-coverage statement to make the remaining
logical dependency in the final theorem explicit.
-/

namespace SuccessorTree.V10

/-- The actual numerical HTop seed family satisfies the REAL
initial-height hypothesis of Algorithm 5.4 at its top original's
canonical E-free level. This is not an externally assumed bound. -/
theorem numericHTopGenerationSeeds_bounded_by_root_freeLevel
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val) :
    (numericHTopGenerationSeeds family K k N
      hAvoidH c blocks hWithin :
        Set (AdmissibleKptNode family)) ⊆
      SuccessorTree.SMTree.Envelope.levelLe
        (T := AdmissibleKptNode family)
        ((finiteNumericH K k N).freeLevel c.val) := by
  intro z hz
  change LevelTree.lev z ≤
    (finiteNumericH K k N).freeLevel c.val
  obtain hRoot | ⟨i,hAncestor⟩ :=
    numericHTopGenerationSeeds_cases family K k N
      hAvoidH c blocks hWithin z (Finset.mem_coe.mp hz)
  · rw [hRoot]
    rfl
  · rw [hAncestor]
    calc
      LevelTree.lev (LevelTree.ancestor
          ((finiteNumericH K k N).kptOriginal family hAvoidH c)
          (hPosition k i.val k) _) =
            hPosition k i.val k := LevelTree.level_ancestor _ _ _
      _ ≤ (finiteNumericH K k N).freeLevel c.val :=
        hWithin i.val i.property

end SuccessorTree.V10
