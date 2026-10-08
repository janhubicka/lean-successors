# Adversarial review of the successor manuscript through Section 5

8 October 2026. Reviewed Lean source: `formalize-envelopes-v8` at
`0dc4dc4d7fb7169ea3acd4461ef734df2c5b0169`, plus the conservative
packaging/cleanup on `audit-envelope-core-v8-20261008`. Reviewed TeX:
the **exact** successor-v8 archive at `b36a2772093c783cd03760edeb49f4e35b655db4`,
with the later validation annotations applied separately.

These are **three deliberately separated adversarial review passes**, not
reports by independent human referees or independently spawned model agents.
No external agent-spawning tool is available here. Each pass had a distinct
audit question and check procedure; conclusions are limited to the evidence.

## Pass A — Lean statements, dependency boundaries and maintenance

**Question:** Is the checked theorem exactly what the paper needs, and is its
proof interface suitable for a later weakening of M1–M3?

**Verified:** Fifteen Section 5 modules contain separate proofs for closure,
one-level E1 pullback, finite-prefix competitors, the strengthened descending
invariant, gap extraction, minimal height and two kinds of independence.
The original successful full/focused GitHub workflows for PR #107 audited
30 theorem endpoints with no `sorryAx` or added axioms.

**Issue A1 (maintenance, resolved on PR #110):** The conclusion of
Proposition 5.5 was previously dispersed among multiple endpoints.
`EnvelopeTheorem.exists_minimalEnvelope` composes them, with explicit
`OneLevelPullback`, boundedness and nonempty-top hypotheses. It adds
no new axiom and no parallel proof body.

**Issue A2 (API clarity, resolved compatibly on PR #110):**
`IsAMEnvelope` was nested inside `AlgorithmRun` although its definition
does not use a run. An outer alias makes the concept available without
breaking existing qualified references. Explicit `EnvelopeTheorem` import
replaces the redundant root import list.

**Issue A3 (future axiom weakening, open):** Do *not* report that envelopes
are independent of M3. `SMTree.level_nonempty` is derived from M3
(see `SuccessorTree/Monoid.lean`) and underlies the total level map,
range arguments, and canonical extension infrastructure. A weakened M3
must supply inhabited levels separately or use a partial-level API.
M2 is used specifically for gap-to-one-level factorisation; E1 is only
used for selected one-level pullbacks and uniqueness. Keep these interfaces
separate in the future generalized theorem.

**Issue A4 (proof organisation, deferred):** Some set/tail bookkeeping in
`AlgorithmRun.I_eq_final_tail` currently takes E1 and a bound on X even
though the level-set recursion itself is combinatorial; consider splitting
a pure run-level lemma if assumptions are weakened. This is a suggestion,
not a diagnosis of unsoundness. The 15 earlier proof modules remain
unchanged in PR #110.

**Certificate boundary:** Kernel compilation of the SMTree/LevelTree API
does not prove the equivalence of the manuscript's set-theoretic tree
definition with the typed LevelTree interface.

## Pass B — mathematical adversary

**Question:** Which hypotheses are *really* necessary for the minimal
envelope claim, and which natural edge cases break a careless reformulation?

**Observation B1 (confirmed):** For an empty X, the paper's algorithm returns
`(Id, ∅)` of height 0. Lean's `AlgorithmRun H X ell` exists for every
chosen ell, and fixes its top set to `{ell}`. The height theorem requires
a top-level member `hTop` and must not be applied to empty X. The new
packaged theorem retains exactly this requirement.

**Observation B2 (confirmed):** The I1/I2 branches and one-level pullback
give the invariant only after showing that the outer map fixes source
levels through i, that the pulled-back closure is parameter-closed above
i, and that one-step inverse images are well-defined. The printed
manuscript's Claim 5.9 omits some of these justifications. Their typed
equivalents are proven in `EnvelopeStage`, `EnvelopeInvariantLevels`,
and `EnvelopeUniqueness`.

**Observation B3 (confirmed):** The minimality argument against finite
envelopes needs the *finite-prefix* closure lemma, then restriction at
the **first input level m' crossing i** before two shape-split operations.
The old manuscript wrote m in one restriction. Its mechanical correction
is valid; the remaining factor-to-crossing calculation needs a full
sentence or lemma.

**Observation B4 (confirmed):** Independence of the interesting levels
does not imply independence of `F^{-1}[X]`; the missing step is the separate
downward induction in `AlgorithmRun.embeddingType_eq`.

**Additional counterexample regression (separate Section 6):** An
independent finite word-enumerator reproduces the earlier B1–B2
`X={01}`, `Y={01,11}` colouring obstruction for word heights
2 through 6. This supports the red warnings but is not a proof by
exhaustion of an infinite claim. B3 repairs type preservation only
conditional on a new proof; it is not part of the Section 5 certificate.

## Pass C — manuscript changes, labels and reader-facing proof

**Question:** Do the validation marks claim more than Lean proves, and
are author choices being silently made?

**Manuscript policy:** Green marks mean a statement has a matching compiled
Lean endpoint. Orange marks mean a restricted or related endpoint is checked
but the printed proof still needs strengthening. Red marks in Section 6
refer to exhibited counterexamples, not failed Lean compilation.

**Safe direct fixes:** British spelling (`minimising`, `cannot`),
the hyphenated `inclusion-minimal`, and the previously repaired
(F_{i+1})/(F) and (m')/(m) misreferences. No change to the
published theorem statements, their axioms, or unapproved B3 is made.

**Precise editorial TODOs:** The claim should state the prefix membership,
followed by the E1 induction and S2 uniqueness; the minimality proof should
cite finite-prefix closure and explicitly show that the factor extends
the prescribed crossing; a separate downward induction must explain
embedding-type independence; nonempty height must be distinguished from
the paper's empty-set convention. The axiom-weakening TODO now points
out the *indirect* use of M3 via `SMTree.level_nonempty`.

**Separate outstanding questions:** The literal LevelTree adapter, the
stronger composition-space projection, and the downstream Section 6
type-to-copy correspondences remain outside this validation. The earlier
four Section 6 red markers are retained pending author revision.

**TeX check:** The annotated manuscript has been built using pdfLaTeX,
bibtex8 and repeated pdfLaTeX; 41 pages, with no missing references or
citations. The affected pages were rendered and inspected. Margin TODOs
increase the length of the review PDF; circulation formatting is unchanged.

## Recommendation and merge discipline

Keep PR #110 a small reviewable **stacked** PR based on #107. Do not
merge PR #106/#107/#110 automatically during mathematical review; #106
has a stale base against the later free-ancestral main. After author
approval, resolve the PR stack against a fresh main, run both workflows,
and merge each localized change independently.

For weakening M3, first prove inhabited levels from the proposed
weaker hypotheses (or adapt the level map), then isolate the exact
one-level gap factor required by minimality, and only afterwards
attempt to generalize the Ramsey pigeonhole/fusion engine.
