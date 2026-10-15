import SuccessorTree.Core
import SuccessorTree.CopyRamsey
import SuccessorTree.V10.All
import SuccessorTree.V10.GPlusInducedAction
import SuccessorTree.V10.GPlusBoundedPalette
import SuccessorTree.V10.GPlusEnvelopePairLift
import SuccessorTree.ShapeEvents
import SuccessorTree.FreeAncestralFiniteRamsey

/-!
# Complete successor library entry point

The minimal import frontier covers the same transitively imported source
modules as the previous 96-line import list. The reusable abstract library
has its own smaller `SuccessorTree.Core` entry point.

This is a complete development umbrella, not a compatibility API. It brings in
both abstract Ramsey proofs, the verified finite V10 construction and the
free-ancestral example. The graph comparison test verifies that shortening the
import list does not silently drop historical proof modules.
-/
