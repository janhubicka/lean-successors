import SuccessorTree.V10.KptCompleteSMTree
import SuccessorTree.V10.KptE1EnvelopeIntegration
import SuccessorTree.V10.HUniformEnvelopeBound
import SuccessorTree.V10.FiniteBigRamseyDegrees
import SuccessorTree.Library.TypeRespecting

/-!
# Public finite relational applications

Exports the normalized Kpt SM-tree with genuine M1–M3, its concrete
one-level pullback/E1, the sharp finite H+ envelope bound, canonical
Gω constructions and the finite big-Ramsey degree for *all* induced
embeddings into a countable age-universal unary/binary structure.
It also exports `AgeTestModel.HasOriginalFiniteBigRamseyDegrees`
and its proven universal-age instance, matching the source paper's
finite-degree definition directly.
The intrinsic binary type-respecting full-profile theorem is also available
separately through `SuccessorTree.Library.TypeRespecting`.

These theorems are specifically about normalized finite families of
irreducible forbidden patterns with the singleton convention encoded
by `NormalizedForbidden`. They are not higher-arity theorems and
are not a replacement for verifying the mathematical correspondence
to an external manuscript's arbitrary-language definitions.
-/
