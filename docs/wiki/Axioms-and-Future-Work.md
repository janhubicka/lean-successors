# Assumptions, extensibility and future axiom relaxation

## Current contract

The formalized abstract theorem is proved for the current `LevelTree` / `STree` / `SMTree` hierarchy with distinguished monoid satisfying **M1, M2 and M3**. The public Ramsey theorem must remain unchanged while validating successor v10. The conditional proof layers should not assume fat-tree A4, a global pruning principle, or a concrete `V10` finite-age extension lemma as extra axioms.

The later applications use specialized finite-model lemmas: corrected B3, honest induced relation records, top seeds, prescribed parameters and the actual Algorithm 5.4 run. Those are **not** new axioms of the abstract theorem.

## Intended generalization — NOT yet proved

The existing duplication assumption is too rigid for prospective variable-word, finite-sums/Hindman and possibly Carlson-type applications. The likely direction is to distinguish:

- **Local extension:** composition, restriction, preservation of finite approximations and canonical successors.
- **Controlled duplication/replay:** enough copying on a specified finite schedule or finite family of test positions, not arbitrary unbounded duplication.
- **Fusion/choice:** a separately stated hypothesis guaranteeing the needed simultaneous finite configurations for the Ramsey induction.

This is a design agenda, not a formally established equivalence to M1–M3 or a claim that the weaker conditions already imply those additional theorems.

## Refactoring prerequisites

1. Map exactly which abstract proof lemmas invoke the full current M3 and whether each use is only finite/scheduled. Keep the trace in code comments or a separate audit file.
2. Separate algebraic map laws, finitary replay, Ramsey input and model-specific `V10` age tests into modules with explicit interfaces.
3. Create an abstract interface for controlled finite replay; prove that the **old M1–M3 structure instantiates it** before migrating the existing theorem.
4. Prove at least one new intended example that fails the old duplication contract but satisfies the weaker one; reject a reformulation that merely reintroduces unrestricted M3 under another name.
5. Maintain exact-head theorem and axiom checks. **Internal and public
   implementation APIs may break**: remove obsolete wrappers instead of
   preserving aliases, and repair downstream consumers directly. A change to
   M1–M3 or the final theorem's quantifiers is a mathematical change and
   still requires a separate proof/statement audit.
6. Do not touch the proof prose of successor v10 in this phase. Future stronger paper and its Lean theory can live on a separate branch.

The safest approach is to **extract a reusable core first**, then generalize it, rather than weaken assumptions inside an unfinished Section 6 application.

## Known invariants worth preserving

- Final shape theorem keeps the full prescribed frozen prefix and right-composition reduction.
- Successor replay needs both source-agreement and target-age preservation, including directed nonedges; a mere node-map inequality is insufficient.
- Source and target code depth must not be confused with actual target level.
- For finite corollaries, all tested maps share the same terminal level before padding.
- Any Section 6 signatures use the *selected* closure and genuine original addresses; duplicates that realize the same type are not interchangeable as named originals.
- Level zero and empty-source cases should be formulated explicitly, not inferred from a positive-level duplication axiom.

See [the proof-route analysis](../shape-proof-routes.md) and [the adversarial audit](Audit-and-Performance.md) before changing the signature of a public `SMTree` theorem.
