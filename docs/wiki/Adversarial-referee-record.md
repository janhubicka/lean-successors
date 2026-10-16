# Adversarial referee audit — 16 October 2026

**Audited reference:** `main` commit
[`1e084eb47aee`](https://github.com/janhubicka/lean-successors/commit/1e084eb47aee283f94ced58290455baf882a5285).
The [full Lean workflow](https://github.com/janhubicka/lean-successors/actions/runs/38916948261)
and [V10 counting workflow](https://github.com/janhubicka/lean-successors/actions/runs/38916948218)
both completed successfully. These are actual GitHub checks, not a claim
that this review ran a local Lean compiler. The subsequent library/API
branch needs **its own exact-head CI** before merging.

The following are three **independent review criteria**, not a claim
that three external mathematicians signed off on this code.
This review separates (A) mathematical statement fidelity,
(B) formal proof trust, and (C) library dependencies and maintenance.
A checked theorem is not automatically identical to uninspected
authorial LaTeX.

## Referee A — theorem statement and manuscript fidelity

1. **Axiomatic core.** `SMTree.shapePreservingRamsey` is unconditional
   relative to an actual `SMTree`, whose contract includes M1–M3.
   The alternative fat-Ellentuck proof is separately checked and has a
   distinct one-dimensional Ramsey input. Neither proof may appeal to
   an unproved fat-tree A4 as an extra *public theorem premise*.
2. **Envelope theorem.** `SMTree.Envelope.exists_minimalEnvelope`
   explicitly assumes `OneLevelPullback` and a nonempty top level.
   It does not state an unconditional empty-set version or grant E1 to
   every abstract SMTree. The Kpt E1 theorem proves precisely the
   needed *source successor exists* property; it does not assert that
   an arbitrary target successor is literally the image of the
   particular chosen source successor.
3. **Finite relational application.** The new
   `V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound`
   quantifies over every induced embedding of the finite original
   unary/binary pattern, not only monotone or ordered copies. The
   adapter handles unary atoms, directed binary atoms, **diagonal**
   binary atoms and negative information. The output K self-embedding
   is ordered and induced.
4. **Hidden scope in universality.** The input `K` must have full
   carrier `Nat`, avoid the normalized forbidden family, and satisfy
   `K.UniversalForNormalizedFamily family`, a strong explicit
   *countable* universality condition. This is appropriate for a
   countable age-universal Fraïssé limit, but the bridge from the
   manuscript's `K_F` and its language/class definitions to this
   interface must be documented or proved; the theorem does **not**
   claim finite-age universality alone is definitionally identical.
5. **Forbidden-family normalization.** The canonical all-false source
   exists because `NormalizedForbidden` excludes neutral
   singletons and requires irreducibility of nontrivial forbidden
   patterns. The result must not be quoted for arbitrary forbidden
   families without the corresponding normalization/reduction.
6. **Residual literal source checks.** The user's current editable
   author `main.tex` is not included in this repository. The
   repo's `manuscript` directory supplies review notes and patch
   generators, not a full editable source. Thus exact textual
   equivalence of the latest proof wording, the `LevelTree`
   set-theoretic adapter, the empty-pattern conventions and the
   finite-age-to-countable-universality implication is *not yet*
   certified by the automated checks. These are explicit review
   obligations, not speculative failures.

**Disposition A:** checked Lean endpoint accepted at its literal type;
do not yet label the *whole author manuscript* unqualified GREEN.

## Referee B — kernel trust and proof provenance

- Each named public result is elaborated into Lean declarations.
  The source scanner rejects `sorry`, `admit`, `sorryAx` and
  source `axiom`/`constant` declarations, respecting Lean nested
  comments and strings. A textual scanner cannot prove theorem
  equivalence or replace kernel elaboration.
- Exact transitive `#print axioms` reports are checked independently.
  In particular, the three final 16 October source modules have
  checkers for the *universal countable K*, the *canonical Gω* and the
  *original Emb(A,K)* endpoints. CI rejects wrong names, extra axiom
  dependencies and incomplete reports.
- The main and dedicated V10 workflows passed at the pinned head.
  The two intermediate merge-run cancellations were superseded by
  these successful exact-head runs and are not failing proofs.
- A possible audit regression is to compile a source module without
  maintaining a corresponding named axiom check. The V10 selector
  fails closed for changed unchecked V10 sources, and its nightly full
  pass matters for declarations on untouched files.
- Independent finite regressions check E-fields, H meet charging,
  original-name addresses, selected-level generation and guarded
  M3/nonedge cases. Such enumerations are diagnostics, not substitutes
  for the symbolic Lean proofs.

**Disposition B:** kernel-checked at the pinned repository head, with
standard Lean axioms only according to passing named CI. New files on
this branch require independent exact-head checks.

## Referee C — minimality, compile time and future axioms

- The root umbrella and V10 assembly were already shortened to small
  terminal import frontiers, with closure-preservation checks. Do not
  reinstate a hundreds-import monolithic public entry point.
- The existing import audit found **zero safe orphan source-module
  candidates** at its recorded snapshot. Filename age or a proof's
  experimental provenance is not evidence of dead code. A proposed
  deletion must have a tested import-graph diff, named endpoint coverage
  and a full build; do not erase proved mathematics by guess.
- Hundreds of V10 modules remain an implementation cost. A
  theorem-oriented `SuccessorTree.Library.Abstract` interface avoids
  importing the concrete age/model layers for downstream abstract work.
  `Library.Applications` and `Library.Examples` keep application
  assumptions outside that core.
- The current concrete M3 supplies unrestricted skipped-level
  duplication, used for both positive-level habitation and replay.
  Weakening it to finite scheduled replay needs two distinct
  replacements: structural level/terminal consequences, and the exact
  successor-code replay equations. The old proof must be preserved
  until such an interface is proved sufficient.
- The same principle applies to `OneLevelPullback`: it belongs at
  the envelope layer, not as an axiom inserted into `SMTree`.
- CI time should be measured from actual runs. Fewer files or more
  parallel jobs alone do not imply a speedup; the Lake workspace
  cache and separate axiom checker account for much of the cost.

**Disposition C:** refactor public imports and documentation; preserve
the proven internal modules for now. No compatibility wrappers are
needed for nonexistent downstream public API consumers.

## Regression criteria for a later structural simplification

Any deletion or axiom refactor must pass (1) full `lake build`;
(2) public import smoke checks; (3) abstract and V10 exact named
transitive-axiom reports; (4) proof-route independence audit;
(5) real M2/M3 induced-record regressions; and (6) a mathematical
statement comparison of changed public propositions. A passing build
alone is insufficient.

## Separate manuscript follow-up

The exact source wording should explicitly distinguish the
normalized theorem's scope from the original language, define the
unary/binary/diagonal correspondence, justify universality for the
target model, and separately handle empty source/forbidden families.
Only reviewed TODO/validation notes may be added to the frozen draft
until authorial editing resumes.
