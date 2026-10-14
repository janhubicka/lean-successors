# V10 local-age insertion and finite forbidden-age checkpoint

Proof SHA: `fc2af03f3b854ec8a14e1356ad82f6074ec91114`.
Full Lean run `38059711091` PASSED, focused V10 audit
`38059711093` PASSED, including all new CheckV10LocalAge*.lean endpoints.

## Validated components

1. `LocalAgeInsertion.lean` proves coordinate insertion/deletion and exact
projection of ordered induced forbidden copies avoiding the new vertex.
2. `LocalAgePartialInsertion.lean` constructs a single genuine finite
partial structure with old ordered L atoms copied exactly and a new
specified L column. E is calculated from explicit transported free cuts;
spacing, downward closure and binary-link E3 are proved.
3. `LocalAgeFreeCut.lean` proves the transported cuts are the canonical
first missing E coordinates, both at the new vertex and at each shifted
old vertex.
4. `LocalAgeForbiddenTest.lean` proves the finite common-socle age-test
contradiction. Only upper vertices joined to the inserted level are
included in the finite witness, so irreducibility supplies their
prescribed crossings. Deleting the inserted level gives a forbidden-free
L-reduct from the old source. Non-neutral forbidden singletons are
excluded by the allowed common socle, not assumed separately.

The finite age test is explicitly restricted to witnesses whose carrier
is bounded in Nat. This matches the manuscript's finite enumerated
L-structures; in this signature boundedness is equivalent to finiteness.

## Boundary and adversarial findings

The insertion level must be positive. At ell=0, an old first vertex of
free cut zero would acquire cut one after inserting coordinate zero;
the resulting E(0,1) contradicts spacing. Lemma 6.51 assumes ell>0.
In all finite inserted models, the new E relation is an auxiliary
partial-structure relation, not an L-atom of forbidden configurations.

This theorem is NOT yet the full local-age boring-extension lemma.
It assumes the finite source, one inserted column obeying the linkage
conditions, the common initial socle, and each linked upper vertex's
prescribed L crossing. A global insertion on every Kpt node, which is
independent of the chosen representing partial structure, commutes with
the actual successor parameter/letter and skips only ell has not yet
been built. The manuscript's mathematical text and four repairs remain
unchanged; source changes are annotations only.

## Separate neutral-socle branch (PR 167)

At proof SHA `5a63b009b01ee9bca4d707d97ce2c2a083243a67`, the focused
V10 build/axiom audit `38060229228` passed. `LocalAgeNeutral.lean`
constructs the new vertex with the allowed empty singleton and no incident
L-relations, keeping the exact transported E-cuts. It derives avoidance of
all normalized forbidden patterns directly: non-neutral forbidden singleton
and binary-irreducible forbidden copies cannot involve the new vertex;
other forbidden copies project back to the source. The three-clause age test
is unnecessary for this neutral branch. This remains a LOCAL finite
transformation; uniform Kpt insertion and the global skipping ShapeMap
are still pending.

When reconciling with the author's statement, remember the chosen finite
L-age witness is represented as a bounded subset of Nat with inherited order;
if the manuscript requires initial-ordinal enumerations, an increasing
renumbering of its upper tail while fixing the first ell+1 positions is a
minor separate coding lemma. No equivalence claim about nullary symbols
is made here.
