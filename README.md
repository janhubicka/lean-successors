# lean-successors

Lean 4 formalisation of **Ramsey theorem for trees with successor operation**
(Balko–Chodounský–Dobrinen–Hubička–Konečný–Nešetřil–Zucker).

## Main endpoints

The public results are theorems of the `LevelTree`, `STree` and `SMTree`
interfaces. The distinguished monoid satisfies M1–M3; no global pruning,
extra amalgamation axiom, or unproved pigeonhole premise is imposed by the
endpoints below.

| Result | Module | Declaration |
| --- | --- | --- |
| Starred Hales–Jewett | `HalesJewett.AlphabetInduction` | `starHJ_finite` |
| Fat-tree A4 | `FatTree.A4ReviewComplete` | `fatTreeA4` |
| Fat-tree Ellentuck | `FatTree.A4ReviewComplete` | `fatTreeEllentuck` |
| Finite-dimensional shape Ramsey, direct fusion | `ShapeFiniteRamsey` | `shapePreservingRamsey` |
| The same theorem from fat-tree Ellentuck | `ShapeEllentuckRamsey` | `shapePreservingRamsey_viaFatEllentuck` |
| Bounded-terminal finite corollary | `ShapeFiniteCorollaries` | `shapeRamsey_bounded` |
| Exact-terminal finite corollary | `ShapeFiniteCorollaries` | `shapeRamsey_exact` |

Module paths are relative to `SuccessorTree`. Both shape proofs share the
relative reduction and dimension induction in `ShapeFiniteInduction`, but use
different one-dimensional Ramsey inputs. Their public statements are unchanged.
See [the proof-route guide](docs/shape-proof-routes.md) before strengthening them.

## Validation boundary

The set-theoretic definition of a tree in the manuscript still needs a formal
adapter to `LevelTree`. The stronger neighbourhood projection to the monoid's
composition-Ellentuck topology is not established by the finite shape theorem
or by the ordinary correspondence between fat trees and shape maps. Later
manuscript applications must be checked separately. The manuscript's TODOs
record these distinctions; a formal endpoint does not certify surrounding prose.

## Build and regression checks

```bash
lake update
lake exe cache get
lake build
lake env lean scripts/CheckShapeRamsey.lean
lake env lean scripts/CheckShapeProofRoutes.lean
```

The normal root build includes both finite corollaries. CI also checks fat-tree
statements, the transitive axioms of the endpoints, and the independence of the
two shape-proof inputs by inspecting elaborated proof dependencies. Axiom checks
allow only `propext`, `Classical.choice` and `Quot.sound`.

The toolchain is Lean `v4.35.0-rc3`. Dependencies are pinned in `lakefile.toml`:
mathlib at `5bd58ac291422a21f412ae354c91e7d172255a2c` and
`lean-ramsey-space-todorcevic` at `54a9eb02f7f7bd2e942e95f7b44fc6f04f48892c`.
CI artifacts retain the resolved manifest and proof-audit logs.
