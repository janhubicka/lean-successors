# Successor v10 — final-form validation/referee checkpoint (16 October 2026)

This is a **review-only note** for the frozen manuscript. It does
not edit the authors' mathematical prose or the four approved repairs.
The current author-edited `main.tex` is not in this Lean repository.

## Checked Lean theorem (supersedes old open-transfer status)

Main [`1e084eb47aee`](https://github.com/janhubicka/lean-successors/commit/1e084eb47aee283f94ced58290455baf882a5285)
passed [full Lean](https://github.com/janhubicka/lean-successors/actions/runs/38916948261)
and [named V10 axiom](https://github.com/janhubicka/lean-successors/actions/runs/38916948218)
workflows. PRs #553–#555 completed:

- `V10.originalBinaryUnary_GOmega_allEmbeddings_bigRamsey_bound`;
- `V10.canonicalNormalizedGOmega_bigRamsey`;
- `V10.universalNormalizedModel_bigRamsey_bound`;
- `V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound`.

The last statement quantifies over *all* finite original unary/binary
induced embeddings `Emb(A,K)`, not just order-preserving maps. It
returns one ordered induced self-embedding of the countable target
reducing the colours to an explicit finite palette. Both directed
orientations, absent atoms, binary diagonals and unary data are part
of the copied pattern. The proof includes the finite H+ count and
the actual Gω/K embedding and colouring transfer.

## Exact manuscript sign-off: adversarial checklist

**A. Age and irreducibility.** Match each author forbidden pattern
and singleton convention to `NormalizedForbidden`. The canonical
all-false infinite age witness depends on the forbidden patterns'
non-neutral singleton and irreducibility assumptions. The theorem
is not freely extendable to arbitrary forbidden families.

**B. Countable universality.** The final K hypothesis is
`K.UniversalForNormalizedFamily family`: every countable
full-carrier model of the normalized forbidden age embeds inducedly
into K. Supply the direct argument/citation for the manuscript's
Fraïssé limit. Membership in the age alone is not sufficient.

**C. Exact signature.** Explicitly match the printed unary and
binary language to separate unary bits, diagonal binary bits, and
off-diagonal *directed* binary bits. Check both truth and nontruth
of every induced tuple; source finite embeddings may be nonmonotone.

**D. Abstract structure.** Confirm the manuscript's set-theoretic
successor tree satisfies the `LevelTree` assumptions and its shape
monoid instantiates the checked `SMTree` axioms as intended.

**E. Edge conditions.** The abstract envelope theorem assumes an
actual nonempty top and E1; concrete Kpt E1 is proved independently.
The final normalized big-Ramsey theorem allows q=0; check that the
author's empty-A and empty-forbidden-list treatments express the
same mathematical conventions.

**F. Scope of Proposition 6.44.** Do not confuse
`numericH_actualRun_uniform_sharp_envelope_bound` (finite genuine
Algorithm 5.4 run and required seed/root hypotheses) with the
subsequently proved **uniform** countable big-Ramsey endpoint.
The latter is an actual separately checked theorem; its conditions
still need matching to the exact source-language proposition.

## Concrete source mismatch: Emb versus OEmb (mandatory TODO)

The inspected reviewed v10 PDF states in **Definition 6.25** that
big Ramsey degrees concern arbitrary `Emb(A,K)`, and **Theorem 6.26**
claims this property. However its displayed proof begins
“a finite colouring χ of `OEmb(A,K)`” and the final palette estimate
counts `OEmb(A,...)`. As written, that proves only the
ordered-source-embedding assertion. The bridge is standard and short,
but **must be stated** rather than changing the definition.

**Precise suggested paragraph (requires author approval before adding
to frozen text):**

> To pass from ordered embeddings to all embeddings, put
> `q=|A|` and consider the finitely many permutations `σ` of its
> vertex set. For each `σ`, let `A_σ` be the enumerated structure
> obtained by transporting the relations of `A` along `σ`.
> Every embedding `f:A→K` has a unique order type `σ` and may
> be written `f=g∘σ` with
> `g∈OEmb(A_σ,K)`. Thus the colouring `χ` induces finitely
> many colourings `χ_σ(g)=χ(g∘σ)` of ordered embeddings.
> Apply the ordered conclusion successively to these finitely
> many colourings, each time pulling the next colouring back
> along the already chosen self-embedding of `K`.
> Subsequent self-embeddings cannot introduce new colours into
> any earlier stabilised class. The composition therefore
> simultaneously bounds all `χ_σ`; the union of their finite
> palettes bounds `χ` on **all** `Emb(A,K)`.

The uniform bound can be taken as at most
`sum_σ b(A_σ)`, or `q! * max_σ b(A_σ)`. In the normalized
Lean implementation the final all-Emb theorem bypasses the textual
omission: it colours *every* finite tuple (with a default value
outside the induced-copy predicate) and transfers this directly.
This is a **genuine manuscript proof-exposition gap**, but the Lean
all-Emb endpoint is separately checked.

For completeness, also document the preceding printed “without loss”
normalizations: if no singleton type is allowed, the only member
is empty; for a nonempty age choose an allowed singleton and
toggle its unary/diagonal truth bits globally to make it neutral,
preserving induced embeddings and irreducibility of pairs.
The assumption that some irreducible two-point type is allowed
requires either a separate degenerate-language argument or a
proof that the construction works without it; do not leave it
under an unexplained WLOG. Finite `K` has finite big Ramsey
degrees trivially, so it need not be force-extended to `ω`
unless a uniform intermediate construction actually requires that.

## Referee disposition

- **Formal kernel proof and transitive axioms at the above main head:
  PASS** according to both successful GitHub workflows.
- **Statement fidelity at normalized finite unary/binary all-Emb(A,K)
  scope: reviewed and documented.**
- **Literal manuscript source correspondence: PENDING** until the
  current author `main.tex` is available for a line-by-line comparison.
  No new Lean `sorry` or extra formal axiom is suggested by this status.
- **Higher arities / weak M3:** explicitly beyond this v10 pass.

All further proposed changes to the frozen manuscript should remain
TODOs/validation markers; the underlying proof text is unchanged.
The active library/referee documentation is in
`docs/wiki/Adversarial-referee-record.md` and
`docs/wiki/Theorems-and-Manuscript.md`.
