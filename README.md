# lean-successors

Lean 4 formalization of **Ramsey theorem for trees with a successor operation**
(Balko–Chodounský–Dobrinen–Hubička–Konečný–Nešetřil–Zucker), including
Hales–Jewett, copy-Ramsey expansion bounds, intrinsic successor events,
shape-preserving Ramsey, fat-tree Ellentuck, envelopes
and finite big-Ramsey applications.

## Verified Lean status (16 October 2026)

At [main commit `1e084eb47aee`](https://github.com/janhubicka/lean-successors/commit/1e084eb47aee283f94ced58290455baf882a5285)
the [full Lean workflow](https://github.com/janhubicka/lean-successors/actions/runs/38916948261)
and the [dedicated V10 transitive-axiom audit](https://github.com/janhubicka/lean-successors/actions/runs/38916948218)
both passed. The verified endpoints now include the *original unary/binary
all-induced-embeddings* big-Ramsey formulation for any countable normalized
age-universal model. This supersedes earlier status notes that the universal
Gω/K transfer remains open.

**Proof vs. manuscript:** the named Lean statements are checked; the
correspondence to the author's latest external editable `main.tex`
still requires a direct definitions-and-hypotheses comparison.
In particular, the forbidden-family singleton/irreducibility
normalization, countable universality of the target, and the original
set-theoretic tree-to-`LevelTree` interface must match. The current
authorial TeX is not stored in this repository. See
[the adversarial referee record](docs/wiki/Adversarial-referee-record.md)
and [manuscript review ledger](manuscript/v10-final-validation-referee-20261016.md).

## Import the theorem library

```lean
import SuccessorTree.Library.Structures    -- lightweight tree/map/monoid and copy systems
-- or:
import SuccessorTree.Library.Abstract      -- M1–M3, HJ, shape Ramsey, fat A4, envelopes
-- or:
import SuccessorTree.Library.Applications  -- Kpt, concrete E1, H+ bound, big Ramsey
-- or:
import SuccessorTree.Library.Examples      -- free-ancestral instance
```

`import SuccessorTree.Library` combines all three. Abstract clients can
continue to import `SuccessorTree.Core` directly. The historical root
`import SuccessorTree` deliberately compiles the **whole research development**,
including implementation and verification material; it is not the
recommended downstream public API.

There are no active clients depending on old public signatures, so we
do not preserve obsolete wrappers. The mathematical statements and
their axiom certificates remain under regression checks.

## Main public endpoints

| Result | Lean declaration |
| --- | --- |
| Finite starred Hales–Jewett | `SuccessorTree.HalesJewett.starHJ_finite` |
| Finite copy-degree bound from Ramsey expansions | `SuccessorTree.RamseyExpansion.copyRamseyDegreeLE_card_expansionTypes` |
| Shape event transport | `SuccessorTree.ShapeMap.mapEvent_injective` |
| Direct shape Ramsey | `SuccessorTree.SMTree.shapePreservingRamsey` |
| Fat-tree Ellentuck shape Ramsey | `SuccessorTree.SMTree.shapePreservingRamsey_viaFatEllentuck` |
| Fat-tree A4 / Ellentuck | `SuccessorTree.SMTree.FatTree.fatTreeA4` / `fatTreeEllentuck` |
| Finite bounded/exact corollaries | `SuccessorTree.SMTree.shapeRamsey_bounded` / `shapeRamsey_exact` |
| Minimal envelopes | `SuccessorTree.SMTree.Envelope.exists_minimalEnvelope` |
| Concrete normalized M1–M3 | `SuccessorTree.V10.normalizedKptSMTree` |
| Concrete envelope E1 | `SuccessorTree.V10.normalizedKpt_oneLevelPullback_for_envelopes` |
| Sharp actual-run finite H+ bound | `SuccessorTree.V10.numericH_actualRun_uniform_sharp_envelope_bound` |
| Canonical Gω big Ramsey | `SuccessorTree.V10.canonicalNormalizedGOmega_bigRamsey` |
| Original unary/binary all-Emb(A,K) theorem | `SuccessorTree.V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound` |
| Free-ancestral finite Ramsey | `SuccessorTree.FreeAncestral.finiteShapeRamsey` |

The final countable application requires a finite normalized
irreducible forbidden family and a full-carrier, forbidden-free target
`K` satisfying `K.UniversalForNormalizedFamily family`: every
countable model of that age embeds inducedly into `K`. All induced
finite pattern embeddings (not just increasing enumerations) are
coloured. The original unary/binary encoding preserves absent and
present directed atoms, unary relations and binary diagonals.
**Higher relation arities and weakened M3 are future projects**, not
claims of this theorem.

## Build and proof audit

```sh
lake exe cache get
lake build SuccessorTree.Core
lake build SuccessorTree.Library
lake env lean scripts/CheckPublicAPI.lean
lake build
python3 scripts/check-successor-proof-integrity.py
```

Full CI checks both shape-proof routes and their independence, fat-tree
A4, exact/finite terminal and envelope statements, with separate named
V10 reports. The transitive `#print axioms` reports permit only
`propext`, `Classical.choice` and `Quot.sound`. V10 performs a
dependency-aware incremental check on changes, plus a scheduled
exhaustive audit. Source reachability is inventoried before any
deletion; a short import list is **not** proof that a module is dead.

The toolchain is Lean `v4.35.0-rc3`; mathlib and
`lean-ramsey-space-todorcevic` revisions are pinned in `lakefile.toml`.
For proof details see [wiki home](docs/wiki/Home.md),
[using the library](docs/wiki/Using-the-library.md),
[theorem/manuscript map](docs/wiki/Theorems-and-Manuscript.md),
[referee audit](docs/wiki/Adversarial-referee-record.md)
and [axiom-relaxation dependencies](docs/wiki/M1-M3-Dependency-Map.md).
