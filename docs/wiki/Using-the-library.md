# Using the Lean successor library

The goal is a mathematical library, not a single monolithic build artifact.
Import the narrowest theorem-facing interface that supplies the required results.

## Imports

```lean
import SuccessorTree.Library.Abstract
-- Add only if needed:
-- import SuccessorTree.Library.Applications
-- import SuccessorTree.Library.Examples
```

`SuccessorTree.Core` remains the implementation-neutral abstract umbrella.
`SuccessorTree.Library.Abstract` gives it a documented public import;
`SuccessorTree.Library.Applications` imports the normalized unary/binary Kpt
results, and `SuccessorTree.Library.Examples` imports the free-ancestral
instance. `SuccessorTree.Library` combines all three. The historical
`import SuccessorTree` intentionally compiles the *entire* development,
including the V10 proof assembly and auxiliary test targets; it is not the
recommended downstream dependency.

## First theorem checks

```lean
import SuccessorTree.Library

#check SuccessorTree.HalesJewett.starHJ_finite
#check SuccessorTree.SMTree.shapePreservingRamsey
#check SuccessorTree.SMTree.shapePreservingRamsey_viaFatEllentuck
#check SuccessorTree.SMTree.shapeRamsey_bounded
#check SuccessorTree.SMTree.shapeRamsey_exact
#check SuccessorTree.SMTree.FatTree.fatTreeA4
#check SuccessorTree.SMTree.FatTree.fatTreeEllentuck
#check SuccessorTree.SMTree.Envelope.exists_minimalEnvelope

#check SuccessorTree.V10.normalizedKptSMTree
#check SuccessorTree.V10.normalizedKpt_oneLevelPullback_for_envelopes
#check SuccessorTree.V10.numericH_actualRun_uniform_sharp_envelope_bound
#check SuccessorTree.V10.canonicalNormalizedGOmega_bigRamsey
#check SuccessorTree.V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound
#check SuccessorTree.FreeAncestral.finiteShapeRamsey
```

These are existing declarations, not restated axioms. The API smoke test
`scripts/CheckPublicAPI.lean` checks them through the new import boundary.
To inspect *complete implicit arguments and hypotheses*, use `#check @Name`
or `#print Name`. A successful `#check` proves resolution, not the
correctness of the mathematical translation from a paper.

## Assumption boundaries

The abstract theorems require `[PartialOrder T]`, `[LevelTree T]`
and an `SMTree S` with the original M1–M3 contract. The minimal-envelope
statement additionally requires `SMTree.Envelope.OneLevelPullback`; this
is **not** an SMTree axiom. The normalized Kpt instance has a separate
proof of that property.

The final finite big-Ramsey theorem uses a finite unary/binary signature,
normalized irreducible forbidden families, and a countable full-carrier
model `K` that avoids the family and satisfies
`K.UniversalForNormalizedFamily family`. The embeddings of the finite
pattern may be **arbitrary induced injections**, including non-monotone
enumerations; the resulting self-embedding of `K` is ordered.
Unary data, both binary orientations, binary diagonal data and absent
relations are part of inducedness. The theorem says nothing about
higher-arity languages or weakening M3.

A countable Fraïssé limit normally supplies the stated universality
through its standard universality theorem. Connecting a particular
author-language Fraïssé class to the exact normalized assumptions is a
separate logical step, not something `#print axioms` can certify.

## Development and verification

```sh
lake exe cache get
lake build SuccessorTree.Core
lake build SuccessorTree.Library
lake env lean scripts/CheckPublicAPI.lean
lake build
python3 scripts/check-successor-proof-integrity.py
python3 scripts/check-core-boundary.py
python3 scripts/audit-import-graph.py
```

`lake build` is the full-source regression; use focused imports for
development. The Lean workflow checks the abstract proof routes,
fat-tree axioms and envelope theorem; the separate V10 workflow checks
all named V10 endpoints using transitive `#print axioms` reports.
That audit permits only `propext`, `Classical.choice` and
`Quot.sound`. The scheduled full run is essential because incrementally
selected scripts alone are not a complete proof-coverage certificate.

The library has no established downstream API clients, so internal
declarations and public imports may be revised without compatibility
wrappers. We should still preserve mathematical statements and
maintain the checker-to-endpoint mapping.
