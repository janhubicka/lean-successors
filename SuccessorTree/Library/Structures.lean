import SuccessorTree.Monoid
import SuccessorTree.CopyRamsey
import SuccessorTree.ShapeEvents

/-!
# Reusable structures, independent of the large Ramsey proofs

This *lightweight* import contains the underlying LevelTree / STree /
ShapeMap / SMTree data and axioms (including the current unrestricted
M1–M3 contract), the intrinsic successor-event/pointed-occurrence
geometry, and generic finite copy systems/Ramsey expansions.

It does not import Hales–Jewett, fat-tree A4, finite-dimensional shape
Ramsey, envelopes or the normalized V10 Kpt application.

This interface is the intended starting point for the later M3 axiom
revision: a new replay/scheduled-duplication structure should be built
alongside the current SMTree and tested independently, without
silently weakening assumptions of already checked theorems.
-/
