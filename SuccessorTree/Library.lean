import SuccessorTree.Library.Structures
import SuccessorTree.Library.Abstract
import SuccessorTree.Library.Applications
import SuccessorTree.Library.Examples

/-!
# Public successor-tree theorem library

This is an explicit theorem-facing umbrella. It does *not* import the
entire development's assembly and audit surface (`SuccessorTree` and
`SuccessorTree.V10.All`). Use narrower imports when possible:

* `SuccessorTree.Library.Structures`: lightweight geometry/algebra axioms;
* `SuccessorTree.Library.Abstract`: the reusable M1–M3 Ramsey mathematics;
* `SuccessorTree.Library.Applications`: normalized Kpt, E1 and the
  original unary/binary finite big-Ramsey theorem;
* `SuccessorTree.Library.Examples`: the free-ancestral instance.

These boundaries are intentionally allowed to evolve: no downstream
public-API users are currently assumed. Proof files retain their own
imports; neither their mathematical statements nor their proofs are
duplicated by this library front door.
-/
