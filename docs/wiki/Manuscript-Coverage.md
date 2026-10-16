# Audited coverage of the successor manuscript (reviewed v10)

**Scope:** The source comparison here uses the reviewed
`successor-v10-relocation-reviewed.pdf` available to the author, as
well as the actual GitHub `lean-successors` theorem declarations at
`main` commit `1e084eb47aee` (16 October 2026).
The current author-editable `main.tex` is not in this repository.
This is a *statement inventory*, not a claim that every printed proof
step has a one-to-one Lean lemma.

**Status legend:** CHECKED = concrete, proved Lean endpoint with
passing named transitive-axiom CI; CONDITIONAL/BRIDGE = a nearby
checked result exists, but the literal printed statement or
representation requires another lemma; NOT EXPORTED = no exact
named theorem endpoint was found in this repository; EXTERNAL =
the statement belongs to a separate Mathlib/research library and
is not independently replayed here.

| Source | Result | Audited Lean status |
| --- | --- | --- |
| 1.6 | Main abstract successor-tree Ramsey theorem | **CHECKED**: `SMTree.shapePreservingRamsey`, with independent fat-tree route |
| 1.7–1.8 | Finite bounded/exact-terminal corollaries | **CHECKED**: `shapeRamsey_bounded`, `shapeRamsey_exact` |
| 1.11 | Shape-preserving Ellentuck | **CHECKED** through typed Ramsey-space application; check exact topological representation |
| 1.12 | Canonical extension of finite shape maps | **CHECKED**: `SMTree.canonicalExtension_unique` |
| 1.17 | Fat-tree Ellentuck | **CHECKED**: `SMTree.FatTree.fatTreeEllentuck` |
| §2–§4 | Fat-tree structure, A1–A4, one-level combinatorial forcing | **CHECKED core**: A4 from independent source-fusion proof; two proof routes audited |
| 5.5 | Envelope minimality / Algorithm 5.4 | **CHECKED conditional theorem**: `Envelope.exists_minimalEnvelope`, requiring genuine E1 and nonempty top |
| 6.4–6.5 | Finite tree/cube of embedding-type sets | **NOT EXPORTED** as concrete boring-extension/cube applications (generic shape Ramsey is checked) |
| 6.9 | Arbitrary boring-extension monoid M1–M3 | **NOT EXPORTED** as a standalone concrete family-of-boring-extensions theorem |
| 6.11 | Milliken tree theorem | **EXTERNAL**: `lean-milliken` project; not re-exported as a checked specialization here |
| 6.13 | Finite Dual Ramsey theorem | **NOT EXPORTED** here; dual-tree project is separate |
| 6.14 | Carlson–Simpson topological theorem | **NOT EXPORTED** as a concrete instance here |
| 6.16–6.17 | Graham–Rothschild and starred version | **NOT EXPORTED** as a concrete substitution-word theorem here |
| 6.19 | Nešetřil–Rödl / Abramson–Harrington | **NOT EXPORTED** as a finite relational Ramsey theorem here; generic copy Ramsey expansion-degree bound is a *different* result |
| 6.26 | Finite big Ramsey degrees for unary/binary free forbidden ages | **CHECKED normalized all-Emb(A,K)** via `V10.universalBinaryUnaryModel_allEmbeddings_bigRamsey_bound`; source normalisation/universality adapter still needs explicit correspondence |
| 6.32, 6.39 | Concrete type tree S-tree and M1–M3 | **CHECKED**: `V10.normalizedKptSMTree` and its component lemmas |
| 6.33 | Concrete E1 | **CHECKED**: `V10.normalizedKpt_oneLevelPullback_for_envelopes` |
| 6.41–6.42 | Ordered age of Gω / induced G+ action | **CHECKED normalized implementations**: G+ enumeration and action modules; source-language bridge review remains |
| 6.44 | Arbitrary-K bounded envelope embedding | **PARTIAL literal match**: concrete numerical actual-run H+ bound CHECKED, plus final global big-Ramsey consequence CHECKED; exact `∀K ∀A ∃b ∀A' ∃C` printed proposition not separately identified as a named export |

## Adversarial discrepancies requiring manuscript TODOs

1. **Emb/OEmb:** Definition 6.25 and Theorem 6.26 use all
   `Emb(A,K)`, while the printed proof starts from
   `OEmb(A,K)`. A finite permutation-type simultaneous
   stabilisation paragraph is necessary. The checked normalized
   Lean endpoint already covers all embeddings.
2. **Normalization:** the printed “without loss” assumptions about
   an allowed empty singleton and a nontrivial irreducible binary
   type need explicit treatment of degenerate ages and unary/diagonal
   relabellings. Do not equate the author's arbitrary forbidden
   family with `NormalizedForbidden` without proof.
3. **Countable age universality:** the printed `K_F`-universal
   definition is about ordered ages and all countable models;
   the Lean `UniversalForNormalizedFamily` hypothesis needs a
   direct language/age translation. Forbidden-freeness alone is
   insufficient.
4. **Envelope Proposition 6.44:** the normalized checked actual-run
   bound does not have the literal quantifier structure of the
   printed proposition; the final global theorem is established by
   further checked constructions. Exporting a direct paper-facing
   proposition would improve maintainability and auditability.
5. **Section 6.1/6.2 applications:** a large abstract theorem
   does not automatically mean each concrete specialization is
   Lean verified. The absence of exported, checked exact applications
   is an implementation coverage task, not a refutation of those
   mathematical results.
6. **Finite/empty cases:** the paper extends finite K by isolated
   vertices to reduce to ω. For the simple assertion “finite big
   Ramsey degrees”, finite K is immediate by finiteness; ensure
   any *uniform bound* asserted in the extension argument is
   actually inherited as stated.

## Recommended finish line

- For **the main abstract theorem and normalized Section 6.3 big
  Ramsey application**, the kernel certificates are green.
  Prepare exact typed manuscript adapters and the source Emb/OEmb
  paragraph to complete literal v10 sign-off.
- For **whole-paper line-by-line formal validation**, separately
  decide whether every listed Section 6.1/6.2 application is
  required inside this repository. If so, give each one a named
  theorem export and exact `#print axioms` regression. Some can
  reuse external already checked libraries without duplicating
  the paper's combinatorial proofs.
- Keep full checked M1–M3 unchanged until future controlled-replay
  axioms can be introduced alongside it.

No compatibility wrappers are required for nonexistent downstream
public-API consumers. Code cleanup should preserve mathematically
useful local lemmas until import/declaration reachability confirms
them removable.
