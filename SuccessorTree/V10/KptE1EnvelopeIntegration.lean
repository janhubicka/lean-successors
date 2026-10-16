import SuccessorTree.V10.KptE1ActualPullbackDefined
import SuccessorTree.EnvelopeInvariant

/-!
# Discharge Section 5 (E1) for the normalized Kpt envelope algorithm

The envelope algorithm does not need a statement saying that any given
target successor lies in the image of a shape map.  Its only E1 input is
`OneLevelPullback`: a defined target step has *some* source step for
the same predecessor, parameter list and letter.

The genuine normalized Kpt proof is stronger: `PullbackDefined` holds
for every shape map in the root-preserving monoid, not just maps which
skip one level.  The statement below is therefore the precise,
unconditional E1 endpoint used by the existing envelope formalization.

This is restricted to the normalized finite unary/directed-binary/
diagonal Kpt model.  It does not assert any new result about the final
universal K→H+→G+ transfer or Theorem 6.26.
-/

namespace SuccessorTree.V10

/-- The actual normalized Kpt SM-tree satisfies the one-level
pullback hypothesis required by the envelope construction; no
additional E1 assumption is needed for this concrete model. -/
theorem normalizedKpt_oneLevelPullback_for_envelopes
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd)) :
    SuccessorTree.SMTree.Envelope.OneLevelPullback
      (normalizedKptSMTree family) := by
  intro D m _hskip
  exact normalizedKpt_oneLevelPullback family D.map D.mem

end SuccessorTree.V10
