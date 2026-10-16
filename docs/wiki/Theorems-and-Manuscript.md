# Verified theorems and manuscript correspondence

This table references actual Lean declarations at the successfully
audited [16 October `main` checkpoint](https://github.com/janhubicka/lean-successors/commit/1e084eb47aee283f94ced58290455baf882a5285).
The newer public-library branch adds import and smoke-test scaffolding
without changing these mathematical statements.

## Principal exported theorem families

| Mathematical statement | Module (prefix `SuccessorTree.`) | Exact declaration |
| --- | --- | --- |
| Finite starred Hales–Jewett | `HalesJewett.AlphabetInduction` | `HalesJewett.starHJ_finite` |
| Finite copy Ramsey degree from expansions | `CopyRamsey` | `RamseyExpansion.copyRamseyDegreeLE_card_expansionTypes` |
| Intrinsic successor event injection | `ShapeEvents` | `ShapeMap.mapEvent_injective` |
| Direct finite shape Ramsey | `ShapeFiniteRamsey` | `SMTree.shapePreservingRamsey` |
| Shape Ramsey via fat Ellentuck | `ShapeEllentuckRamsey` | `SMTree.shapePreservingRamsey_viaFatEllentuck` |
| Fat-tree A4 | `FatTree.A4ReviewComplete` | `SMTree.FatTree.fatTreeA4` |
| Fat-tree Ellentuck | `FatTree.A4ReviewComplete` | `SMTree.FatTree.fatTreeEllentuck` |
| Bounded-terminal finite corollary | `ShapeFiniteCorollaries` | `SMTree.shapeRamsey_bounded` |
| Exact-terminal finite corollary | `ShapeFiniteCorollaries` | `SMTree.shapeRamsey_exact` |
| Minimal nonempty top-level envelopes | `EnvelopeTheorem` | `SMTree.Envelope.exists_minimalEnvelope` |
| Normalized concrete M1–M3 | `V10.KptCompleteSMTree` | `V10.normalizedKptSMTree` |
| Kpt successor one-level pullback | `V10.KptE1ActualPullbackDefined` | `V10.normalizedKpt_oneLevelPullback` |
| Envelope E1 for concrete Kpt | `V10.KptE1EnvelopeIntegration` | `V10.normalizedKpt_oneLevelPullback_for_envelopes` |
| Sharp finite H+ envelope bound | `V10.HUniformEnvelopeBound` | `V10.numericH_actualRun_uniform_sharp_envelope_bound` |
| Uniform fixed Gω theorem | `V10.KptBigRamseyNormalizedTheorem` | `V10.normalizedKpt_GOmega_self_bigRamsey_bound` |
| Original all-Emb(A,Gω) unary/binary | `V10.KptOriginalBinaryUnaryBigRamsey` | `V10.originalBinaryUnary_GOmega_allEmbeddings_bigRamsey_bound` |
| Canonical Gω without user-supplied countable C+ | `V10.KptCanonicalGomegaBigRamsey` | `V10.canonicalNormalizedGOmega_bigRamsey` |
| Normalized age-universal K big Ramsey | `V10.KptUniversalAgeBigRamsey` | `V10.universalNormalizedModel_bigRamsey_bound` |
| Original all-Emb(A,K) big Ramsey | `V10.KptUniversalAgeBigRamsey` | `V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound` |
| Free-ancestral history finite Ramsey | `FreeAncestralFiniteRamsey` | `FreeAncestral.finiteShapeRamsey` |

The `Library.Abstract`, `Library.Applications` and
`Library.Examples` entry points collect the reusable endpoints.
`V10.All` and the old root import are *proof assembly* targets,
not additional mathematical assumptions. More lower-level reusable
statements are available in `SMTree`, `Envelope`, `FatTree`,
`HalesJewett`, `V10` and `FreeAncestral`; the public smoke test
checks representative principal endpoints, not every helper lemma.

## Exact final Theorem 6.26-style formal statement

`V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound` has
parameters for a finite signature (`db` binary and `du` unary
predicates), a finite `List (NormalizedForbidden db du db)`, and a
model `K : AgeTestModel db du db`. The hypotheses are:

- **Full carrier:** `∀ i, i ∈ K.carrier`;
- **Forbidden age:** every listed forbidden pattern avoids `K`;
- **Countable universality:**
  `K.UniversalForNormalizedFamily family`, meaning every
  forbidden-free full-carrier countable model `W` admits an induced
  embedding `W → K`.

For every finite `q`, original unary and directed binary pattern,
and finite colouring of **all induced embeddings**
`binaryUnaryAllEmbeddings K PB PU`, a single ordered induced
self-embedding `e : K.InducedEmbedding K` reduces the colours to
an explicitly finite bound derived from
`boundedGPlusPaletteIndices` and
`numericHTopUniformPaletteHeight`. **The original coloured finite
embedding need not be order-preserving.** The binary diagonal
`B(x,x,r)` is stored separately from off-diagonal directed relations;
positive, negative and reversed tuples, and unary atoms, are
all tested.

A countable Fraïssé limit of the matching free forbidden age supplies
the required age-universality under the usual hypotheses, but the
**exact author's age-to-`NormalizedForbidden` dictionary** must be
checked before claiming literal equivalence with the source theorem.
The model's mere forbidden-freeness does *not* imply countable
universality. Neutral forbidden singleton patterns and reducible
forbidden patterns are outside the normalized canonical all-false
construction unless reduced to the checked class.

## Additional proof work beyond printed prose

- A generic `FiniteCopySystem`/`RamseyExpansion` interface provides an
  expansion-type upper bound on copy Ramsey degrees, without requiring
  rigidity of embeddings, and `IntrinsicEvent`/`PointedOccurrence`
  transport is independent of the concrete Kpt model.
- Starred HJ was proved by an explicit forcing/alphabet induction rather
  than assumed as an unverified one-dimensional input.
- The fat-tree A4 proof uses typed history/trace replay and independent
  source fusion. An elaborated-dependency check guards independence
  of the two shape Ramsey proofs, which share only the finite
  dimensional induction.
- Exact finite terminal bounds require common M3 padding; zero
  terminal level is separate.
- M2's corrected non-edge/compatible B3 age test uses an actual
  **finite L-only** forbidden witness; no fictional E expansion.
- The finite H+ bound counts actual selected I1/I2/I3 events,
  original vertex addresses and the sharp forest-meet closure.
- Concrete Kpt E1 proves existence of a pulled-back **source**
  successor; it does not claim equality with an arbitrary target
  successor under F.
- Canonical Gω is realized using an honest all-false forbidden-free
  countable witness. The universal K result transfers via induced
  embeddings and preserves the finite palette.

## Adversarial printed-proof mismatch

In the reviewed v10 PDF, Definition 6.25 defines big Ramsey
degrees for **all** `Emb(A,K)`, and Theorem 6.26 asserts the
same; the printed final proof begins with a colouring of
`OEmb(A,K)` and bounds ordered copies only. This leaves a
short but necessary step: split embeddings by the finitely many
order types `σ∈Sym(q)`, regard each as an increasing embedding
of the corresponding relabelled `A_σ`, and successively
stabilize the induced colourings, pulling each back through the
previous self-embedding. The resulting composition bounds
all `Emb(A,K)` (by a finite sum of ordered palettes).
The checked Lean proof **already colours all tuples directly**,
so the defect is editorial, not an open formal theorem.
Exact proposed wording is in
[the manuscript reviewer note](../../manuscript/v10-final-validation-referee-20261016.md).

## Remaining literal manuscript-fidelity checks

The current author-edited v10 `main.tex` is not part of this
repository, so CI cannot directly compare its text to theorem types.
Before marking the *entire paper* GREEN, review the exact
set-theoretic tree-to-`LevelTree` adapter; the original
finite-language-to-normalized Boolean representation; forbidden
singleton and irreducibility hypotheses; the Fraïssé model's
countable universality; q=0/empty-forbidden-list conventions; and
the distinction between the finite-H+ actual-run proposition
and the final countable Emb(A,K) theorem.

The latest final Lean transfer is **checked**, not “still open”.
Higher relation arities, weaker replay axioms, and alternative
forbidden families are deferred. The author manuscript should
remain frozen except reviewed TODOs and validation markers.
See [the adversarial report](Adversarial-referee-record.md) and
[manuscript validation note](../../manuscript/v10-final-validation-referee-20261016.md).
