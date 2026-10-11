import SuccessorTree.V10.MeetTrace
import Mathlib.Tactic

/-!
# Binary relation patterns in the v10 H-construction

A finite binary language (including the two orientations of each relation)
is encoded by a finite tuple of Boolean relation bits. A first positive
disagreement in this tuple identifies the earliest nonempty base pair of the
higher-generation original, provided all earlier complete relation tuples
agree at the smaller generation. The partial-type meet adapter remains
separate.
-/

namespace SuccessorTree
namespace V10

/-- Each coordinate records one directed binary atomic relation. -/
def bundledTrace {d : Nat}
    (pairBits : Nat → Nat → Fin d → Bool)
    (k source gen earlier level : Nat) : Fin d → Bool :=
  fun r => traceBit (fun a b => pairBits a b r) k source gen earlier level

/-- A first positive mismatch in a finite binary relation pattern forces a
nonempty base relation at that block and no earlier nonempty pair to the
higher-generation original. -/
theorem bundledPositiveMismatch_firstNeighbour
    {d : Nat} (pairBits : Nat → Nat → Fin d → Bool)
    (k i j m n p : Nat)
    (hmn : m < n) (hmk : m < k)
    (hbefore : ∀ (u : Nat), u < p →
      bundledTrace pairBits k i n u m =
        bundledTrace pairBits k j m u m)
    (hdiff : bundledTrace pairBits k i n p m ≠
      bundledTrace pairBits k j m p m) :
    (∃ r : Fin d, pairBits p i r = true) ∧
    (∀ u < p, u < i → ∀ r : Fin d, pairBits u i r = false) := by
  have hdiffCoord : ∃ r : Fin d,
      traceBit (fun a b => pairBits a b r) k i n p m ≠
      traceBit (fun a b => pairBits a b r) k j m p m := by
    by_contra hnone
    apply hdiff
    funext r
    by_contra hneq
    exact hnone ⟨r, hneq⟩
  obtain ⟨r, hr⟩ := hdiffCoord
  have hfirst := positiveMismatch_firstNeighbour
    (fun a b => pairBits a b r) k i j m n p
    hmn hmk (by
      intro u hu
      exact congrFun (hbefore u hu) r) hr
  refine ⟨⟨r, hfirst.2.1⟩, ?_⟩
  intro u hu hui s
  have hfull := congrFun (hbefore u hu) s
  have hsmall : traceBit (fun a b => pairBits a b s) k j m u m = false :=
    traceBit_small_at_own (fun a b => pairBits a b s) k j m u hmk
  have hhigh : traceBit (fun a b => pairBits a b s) k i n u m = false :=
    hfull.trans hsmall
  simpa [traceBit, hui, hmn] using hhigh

end V10
end SuccessorTree
