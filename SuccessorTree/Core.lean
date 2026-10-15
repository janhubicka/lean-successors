import SuccessorTree.HalesJewett.AlphabetInduction
import SuccessorTree.ShapeFiniteRamsey
import SuccessorTree.FatTree.A4ReviewComplete
import SuccessorTree.ShapeEllentuckRamsey
import SuccessorTree.ShapeFiniteCorollaries
import SuccessorTree.EnvelopeTheorem

/-!
# Reusable successor-tree Ramsey core

This import is intentionally independent of the finite relational application
in `SuccessorTree.V10`, the free-ancestral example and the non-precompactness
applications.  Import `SuccessorTree.Core` to use the current M1--M3
abstract theorem and its two independent shape-Ramsey proof routes.

The root `SuccessorTree` umbrella continues to import all applications
and proof-audit modules, so the existing complete `lake build` remains a
full-library regression rather than a reduced build.

No replacement axioms, concrete finite-age hypotheses, or unfinished
Section 6 transfer are introduced by this entry point. Future work on a
weaker duplication/replay interface should start below these endpoints.
-/
