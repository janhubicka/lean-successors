# Active formalization and maintenance roadmap

Updated 15 October 2026. The early scaffold (which still described starred
Hales–Jewett as an unproved input) has been superseded; its history is in Git.
See the [maintained wiki](docs/wiki/Home.md) for exact statements and
[assumption boundaries](docs/wiki/Axioms-and-Future-Work.md).

## Status

- **Checked abstract core:** Hales–Jewett, successor `LevelTree`/`STree`/`SMTree`,
  M1–M3, both shape-Ramsey proof routes, typed fat-tree A4/Ellentuck, finite
  bounded/exact terminal corollaries.
- **Checked concrete scope:** normalized finite-signature Kpt M1–M3 and
  actual-run finite numerical H+ envelope bound.
- **Unfinished v10:** universal induced K→H+→G+ transfer, sufficiently long
  canonical finite approximants, colouring pullback and final Theorem 6.26;
  separately confirm empty/boundary cases and literal author-language
  normalisation. Higher arities are deferred.

## Immediate maintenance

1. Preserve the theorem statements and transitive `#print axioms` checks.
   Introduce dependency-aware V10 CI on `main` pushes, parallelize the
   independently checked proof scripts and retain an exhaustive nightly run.
2. Collect an import-graph inventory of every source/check module, rank orphan
   candidates, examine the actual downstream imports and remove only confirmed
   obsolete experiments in a **separate reviewed change**.
3. Reduce oversized `lean.yml` and source umbrellas incrementally while keeping
   all named endpoints and the two independent proof-route checks intact.
4. Profile the largest remaining Lean elaboration bottlenecks, warning sites
   and Lake cache behavior. Track measured time before and after, not merely
   fewer lines or fewer CI commands.
5. Keep the manuscript prose frozen apart from reviewed TODO/validation
   markers while Section 6 is being finished.

## After current v10 validation

Extract a lightweight reusable core with stable public imports. Then assess
weakening the full M3 duplication requirement to a finitary controlled-replay
interface supporting variable words, finite sums/Hindman, and potentially
Carlson-type theorems. This is **future work**, not an assumption already
validated in the successor draft.

## Verification

```bash
lake exe cache get
lake build
lake env lean scripts/CheckShapeProofRoutes.lean
python3 scripts/select-v10-checks.py
python3 scripts/run-v10-checks.py --jobs 3
python3 scripts/audit-import-graph.py
```

See [CI and adversarial audit details](docs/wiki/Audit-and-Performance.md).
