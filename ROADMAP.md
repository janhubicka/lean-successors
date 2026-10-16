# Validation and maintenance roadmap

**Checkpoint:** 16 October 2026, main `1e084eb47aee`:
[full Lean](https://github.com/janhubicka/lean-successors/actions/runs/38916948261)
and [V10 counting/axiom audit](https://github.com/janhubicka/lean-successors/actions/runs/38916948218)
passed at the exact same commit.

## Checked at the Lean theorem interfaces

- Abstract M1–M3 successor finite shape-Ramsey theorem, two distinct
  one-dimensional proof inputs, starred Hales–Jewett, typed
  fat-tree A4/Ellentuck, bounded/exact-terminal finite Ramsey.
- Abstract minimal-envelope theorem with explicit one-level pullback
  and nonempty-top hypotheses.
- Concrete finite unary/binary normalized Kpt M1–M3, the actual
  Kpt E1 pullback, and the sharp numerical H+ actual-run bound.
- Canonical Gω finite big Ramsey and self big Ramsey for any countable
  forbidden-free **age-universal K**; original unary/binary source
  copies include all induced `Emb(A,K)`, not merely ordered `OEmb`.
- Free-ancestral history-tree instance.

## Outstanding manuscript-fidelity verification

1. Compare the **current editable author v10 `main.tex`**, not stored
   in this repository, to exact Lean theorem types. Preserve approved
   proof repairs and authorial prose; add only TODO/validation markers.
2. Check the correspondence between source irreducible forbidden
   patterns/singletons and Lean `NormalizedForbidden`. The canonical
   neutral all-false model explicitly uses those restrictions.
3. State the paper Fraïssé target's **countable** universality and
   justify `UniversalForNormalizedFamily` for its normalized
   representation. Forbidden-freeness alone is not this property.
4. Confirm the paper's set-theoretic tree representation satisfies
   `LevelTree` and the boundary conventions for empty A/family.
5. Distinguish actual finite Algorithm 5.4/H+ counting from the
   separately checked universal big-Ramsey transfer. Do not equate
   a narrow finite statement with unqualified Proposition 6.44.

## Maintenance

- Keep theorem-oriented imports
  `SuccessorTree.Library.Abstract`, `Applications`, `Examples`.
  The root umbrella is a **full research build**, not a user API.
- Compile a public-API smoke test in CI; keep independent transitive
  `#print axioms` certificates and two shape proof routes.
- Previous source reachability found **no safe orphan proof modules**.
  Audit private helpers and redundant local derivations before deleting
  anything; never delete solely because a filename says `Review`.
- Remove obsolete *compatibility wrappers* freely: no active API
  consumers must be supported. Retain genuine mathematical results
  and update internal consumers directly.
- Continue CI timing/performance measurements and split abstract/core
  iteration from the expensive comprehensive V10 source build.
- Synchronize `docs/wiki` to the GitHub Wiki once its first page
  has been initialized; source-controlled docs remain primary.

## After manuscript sign-off

Research a controlled finite-replay/duplication interface to relax M3
for variable words and finite sums, perhaps Carlson. Preserve the
verified old theorem and replace **both** (a) level-habitation/
terminal-padding consequences and (b) exact successor-code replay.
Higher arities are deferred. See [M1–M3 dependency map](docs/wiki/M1-M3-Dependency-Map.md)
and [adversarial referee record](docs/wiki/Adversarial-referee-record.md).
