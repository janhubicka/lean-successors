# M1–M3 dependency inventory and generalization boundary

**Purpose.** This is a source-driven inventory for future generalizations of
the successor-tree Ramsey theorem to variable words, finite sums and related
combinatorics. It is not itself a proof that weakened axioms suffice. The
current verified M1–M3 theorems and the now-checked normalized unary/binary Section 6
Lean transfer remain unchanged; literal external manuscript correspondence remains separately reviewable.

## Abstract axioms presently packaged in `SMTree`

`SuccessorTree/Monoid.lean` packages four logically different ingredients:

- **M1 identity/composition:** `id_mem` and `comp_mem` of the distinguished
  family of shape-preserving maps.
- **M1 fusion closure:** `fusion_mem` for a pointwise stable infinite
  sequence of distinguished maps.
- **M2 one-gap factorization:** `m2`, with a *literal* factorization through
  a map whose range skips precisely the missing target level, agreeing on the
  entire specified initial segment.
- **M3 unrestricted duplication:** `m3` supplies a monoid map for **every**
  pair `n < m`, inserting exactly one skipped level and replaying
  successor codes along the required upper-node order condition.

The `LevelTree` interface does not assume all levels are inhabited or
globally pruned. This is intentional, and it matters for axiom relaxation.

## Direct source uses (snapshot 15 October 2026)

These are counts of **textual** `H.m3`, `H.m2` and `H.fusion_mem`
occurrences in project Lean source, rather than a transitive proof-term
dependency graph. Some occurrences refer to the same selected witness.

| Field | Direct source locations | Main proof role |
| --- | --- | --- |
| `H.m3` (8 textual uses) | `Monoid.lean` (2), `Replay.lean` (4), `ShapeFiniteCorollaries.lean` (2) | Level inhabitation/positive-level pruning; chosen duplication map; exact-terminal padding |
| `H.m2` (4) | `Canonical.lean` (2), `ShapeSplit.lean` (2) | Gap extraction and literal initial-segment factorization |
| `H.comp_mem` (1) | `Approximation.lean` | Closure of distinguished maps under composition |
| `H.fusion_mem` (7) | `Canonical`, `ShapeFusion`, `ShapeRamseyFusion`, `ShapeBlockForcing`, `RamseySpace/Finitization`, `FatTree/ShapeCorrespondence` | Stable-limit closure in canonical and fusion constructions |

The chosen `H.duplicate` map is referenced approximately 46 times across
the replay/fat-tree proof files. `duplicateHistoryLetter` occurs 17 times
across 8 files. Those transitive **clients** are just as important as the
four direct `H.m3` selection sites in `Replay.lean`; replacing the field
without inspecting them would be unsound.

### Nonemptiness is a real mathematical dependency

`SMTree.level_nonempty` calls M3 with `n=0, m=k+1` and uses the
`SkipsOnly` range equation to produce a node at any prescribed level
`k`. The total function `H.levelMap F : Nat → Nat` is defined using this
fact. M3 also proves immediate successor existence at every *positive*
level in `SMTree.exists_immediateSuccessor_of_level_pos`.

Consequently, merely weakening the duplication rule in `Replay.lean`
without replacing these structural consequences would leave the entire
approximation/shape-map interface ill-founded. A generalized abstract
interface should explicitly account for the level-habitation premise
(or derive it from a weaker axiom) **before** redefining `levelMap`.

### Replay and finite terminal padding are separate obligations

`Replay.lean` defines `duplicate` from `H.m3 n m (n<m)` by
`Classical.choose`; its precise successor-code equation is exposed by
`duplicate_rule`. `replayDup` chooses the source level from an actual
occurrence in the support prefix and the target level from the tail
position. `replayTail` then composes these maps. The full replay
identities use more than mere existence of a level-skipping map: the
successor equations and compatibility through composition are necessary.

`ShapeFiniteCorollaries.paddingLetter` uses the **specific** instance
`H.m3 0 t` for positive terminal `t`. This ensures a fixed one-gap
duplication can be iterated to reach an exact finite target level. The
terminal-zero case is handled separately. A future limited-duplication
axiom must either support this controlled padding operation or replace
the finite exact-terminal corollary by a different argument.

### M2 is not just an order-theoretic split

The direct uses of `H.m2` in `Canonical` and `ShapeSplit` retain the
actual shape-map factorization, skipped-level certificate and initial
segment agreement. The normalized `V10` instance proves this from
finite common-socle L-age geometry. Weakening M3 does not by itself
weaken or discharge M2. Keep the abstract M2 theorem independent of
the concrete V10 forbidden-copy construction.

## Proposed staged refactoring

1. **Keep the present v10 theorem untouched.** Preserve the exact
   M1–M3 `SMTree` instance and named transitive-axiom checks while
   Section 6's final universal transfer remains in progress.
2. **Separate structural consequences from duplication choices.** Identify
   the minimal assumptions giving inhabited levels, total level maps,
   positive-level successors, composition and fusion. Ensure the old
   `SMTree` proves this interface first.
3. **Specify *finite scheduled replay*.** Instead of demanding a map for
   every unbounded pair `n<m`, express the exact finite set of source
   occurrences, target insertion levels, successor codes and controlled
   compositions needed for one starred-line construction. Require
   *consistent maps for the whole finite schedule*, not independently
   chosen witnesses that might disagree.
4. **Prove the original M3 implies scheduled replay.** A proof here uses
   the existing `duplicate_rule`, `replaySource_lt`, and composition
   identities. Avoid new global `axiom` declarations or an opaque
   convenience lemma that assumes the goal.
5. **Replace the one-dimensional input first.** Preserve the shared
   finite-dimensional induction `ShapeFiniteInduction`, then prove the
   direct and fat-tree one-level inputs from the weaker interface.
   Audit these as *separate* proof routes.
6. **Check at least one genuinely new model** (variable-word style or
   finite-sums) where the old unrestricted M3 condition is inappropriate.
   A reformulation equivalent to M3 is not a successful generalization.
7. **Migrate downstream consumers directly.** User-approved internal/API
   breaks are fine; no compatibility wrappers should be retained.
   Changes to mathematical theorem statements and proof assumptions must
   still be flagged as substantive.

## Adversarial acceptance criteria

- The generalized one-level theorem has no hidden unconditional A4,
  pruning, infinitary replay or extra amalgamation assumption.
- Its finite replay witnesses are coherent across *all* source letters,
  rather than different arbitrary copies for each occurrence.
- Level-zero, empty support and exact-terminal boundary cases are
  separately proved.
- The induced map and colouring action retain full source prefix
  agreement and right-composition reduction.
- The old `SMTree` instance proves the new assumptions, the existing
  finite-dimensional theorem is recovered, and the complete `V10`
  normalized model still compiles with standard Lean axioms.
- The two proof routes remain independently checked via
  `scripts/CheckShapeProofRoutes.lean`; exact-head CI and
  `#print axioms` are recorded.

There is **no need** to decide the final weaker axiom now. This inventory
isolates which current uses must be replaced and which mathematical
consequences the replacement must preserve.
