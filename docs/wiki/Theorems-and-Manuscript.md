# Theorems, additional lemmas, and manuscript scope

## Established exported endpoints

| Mathematical content | Module (prefix `SuccessorTree.`) | Exact declaration |
| --- | --- | --- |
| Finite starred Hales–Jewett | `HalesJewett.AlphabetInduction` | `starHJ_finite` |
| Fat-tree Todorčević A4 | `FatTree.A4ReviewComplete` | `SMTree.FatTree.fatTreeA4` |
| Fat-tree Ellentuck theorem | `FatTree.A4ReviewComplete` | `SMTree.FatTree.fatTreeEllentuck` |
| Direct shape Ramsey theorem | `ShapeFiniteRamsey` | `SMTree.shapePreservingRamsey` |
| Shape Ramsey by fat-tree Ellentuck | `ShapeEllentuckRamsey` | `SMTree.shapePreservingRamsey_viaFatEllentuck` |
| Bounded-terminal finite corollary | `ShapeFiniteCorollaries` | `SMTree.shapeRamsey_bounded` |
| Exact-terminal finite corollary | `ShapeFiniteCorollaries` | `SMTree.shapeRamsey_exact` |
| Concrete normalized model of M1–M3 | `V10.KptCompleteSMTree` | `V10.normalizedKptSMTree` |
| Concrete Kpt source-successor pullback (E1) | `V10.KptE1ActualPullbackDefined` | `V10.normalizedKpt_oneLevelPullback` |
| Envelope algorithm E1 for normalized Kpt | `V10.KptE1EnvelopeIntegration` | `V10.normalizedKpt_oneLevelPullback_for_envelopes` |
| Sharp finite numerical `H^+` envelope bound | `V10.HUniformEnvelopeBound` | `V10.numericH_actualRun_uniform_sharp_envelope_bound` |

The last theorem is explicitly parameterized by a finite normalized forbidden family, finite model `K` avoiding that family, a positive `k`, root and admissible top seed blocks, a **genuine AlgorithmRun**, and the stated forbidden-pattern size constraint. Its inequality bounds selected levels in that concrete run. It is not the complete universal statement of Proposition 6.44. Read its Lean type before using it as an external premise.

The library also contains finite-type and model verification modules not listed here. Successful local files are not automatically exported manuscript theorems; `V10/All.lean` is an assembly/test umbrella, not the place to hide missing hypotheses.

## Added proof structure beyond the printed text

- **Supported starred HJ / alphabet induction:** explicit combinatorial forcing/fusion with a support prefix. This replaces treating starred HJ as a tacit input.
- **Fat-tree A4:** a typed fixed-stem pigeonhole theorem with its history/replay/trace transfer, giving unconditional A4 and Ellentuck instead of assuming A4.
- **Two one-dimensional inputs, one induction:** both finite shape proofs use `ShapeFiniteInduction`. An axiom/dependency audit distinguishes them rather than relying merely on textual import inspection.
- **Finite terminal cases:** coherent bad-colouring compactness and exact-terminal padding based on a common positive terminal level.
- **M2 repair:** use the actual finite common-socle `L`-age condition for the corrected prescribed B3; nonedges must be handled in induced copies. Do not assume an arbitrary `E` expansion on an `L`-only age witness.
- **M3 and Section 6 record precision:** keep directed binary bits, unary and diagonal data and the absence of edges; linked-clone projection is not indiscriminate upper-column copying.
- **Actual Algorithm 5.4 counting:** isolate original-name addresses, selected generations, I1/I2 real meet charges, I3 failed-B3 signatures and the sharp forest meet closure. This makes the numerical `H^+` estimate checkable independently of the final universal transfer.
- **Concrete E1 pullback:** the canonical target parameter has an empty/singleton source preimage, and complete L+ type reindexing preserves predecessor, canonical source parameter, all E and L atoms, and the terminal letter. The source successor uses an actual neutral-spacer admissibility witness; source *existence* is what E1 requires, not equality of the chosen target with an F-image.

These are proof engineering and repair notes, not a claim that every such addition has already been written into the frozen manuscript.

## Manuscript comparison: what remains

- The set-theoretic tree definition still needs a precise adapter to the Lean `LevelTree` representation where used.
- The normalised finite model currently handles **unary, directed binary and diagonal** records, not arbitrary arities.
- Section 6 requires the uniform induced `K → H^+ → G^+` embedding/enumeration and bounded-envelope transfer **for all finite source copies**, including exact source-target quantifier order.
- The `G^+` canonical representations, induced relation preservation, finite prefix/upper-node representation and colouring pullback must be assembled at the *actual* Algorithm 5.4 seeds and sufficiently long finite approximants.
- Check empty structures, forbidden-free family, singleton conventions, and any equality assumptions separately rather than inheriting a nonempty case by silence.
- The final big-Ramsey Theorem 6.26 is **open at the exact manuscript scope** until all those adapters and transfer steps are discharged and audited.

For changing status at the level of named PRs or check runs, consult [the Section 6 ledger](../v10-section6-final-assembly-20261015.md) and current [repository PRs](https://github.com/janhubicka/lean-successors/pulls), not historical summaries in comments.
