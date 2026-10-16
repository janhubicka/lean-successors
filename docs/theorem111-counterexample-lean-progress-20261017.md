# Formalization status: direct-monoid Theorem 1.11 counterexample

Working branch: `formalize-theorem111-counterexample-20261017` (PR #565).
Reference mathematical argument: `docs/theorem111-zfc-counterexample-20261016.md`.
No manuscript source has been changed.

## Kernel-checked foundation (focused CI 38975937763)

- `Counterexample/NowhereDense.lean`: right compatibility (common algebraic right multiple), pairwise right-incompatible families, proper late gaps, the no-self-factorization lemma, and the local-escape lemma giving a disjoint nonempty basic subneighborhood.
- Same module: proved existence of late proper gaps for the verified free-ancestral one-letter arity-one SMTree.
- `Counterexample/MaskCodes.lean`: strict level-map transport of ancestral parameters, mandatory code avoidance of root index 0, root-marker existence and code remapping injectivity.
- `Counterexample/SupportRigidity.lean`: generic proof that a fixed infinite support witness is contained in **at most one** support of an almost-disjoint family.
- The exact-name `CheckTheorem111Counterexample.lean` transitive-axiom audit passed.

## Extensions being compiled (do not count as verified before CI succeeds)

- `Counterexample/Topology.lean`: upgrade local escape to actual `IsNowhereDense` in the **monoid Ellentuck topology**, via the ordinary topological closure criterion.
- `Counterexample/StretchHistory.lean`: recursively define every finite history of the candidate infinite marked map at any increasing prescribed levels `levels : ℕ → ℕ` with `levels 0=1`, padding gaps with the root-parameter marker. Prove marker padding is injective and the original history is its prefix. At present this is the raw function on all histories, **not yet a certified ShapeMap**.
- The focused CI workflow compiles every module and audits all exported theorem axioms; previous compiler passes found only dependent-index/topology-elaboration issues, corrected locally on the branch.

## Unfinished proof obligations (essential to the counterexample)

1. Show `markedNode` is an injective full shape-preserving map of the free-ancestral tree, including weak-successor preservation and the level law.
2. Prove retained successor codes cannot use original-root parameter and every skipped level has the root marker, even after a pure outer shape map.
3. Formalize the **concrete compatibility lemma**: if `G(r)=s` and G has a common right-composition multiple with `H ∘ Q_A` (H pure), the infinite set `D_G^H` lies in A.
4. Construct continuum many pairwise almost-disjoint supports via binary-sequence prefixes, and prove the fixed-G uniqueness lemma using (3).
5. Formalize ZFC transfinite recursion enumerating all pure maps and selecting a pairwise right-incompatible transversal hitting each pure cone, with no CH assumption.
6. Apply the checked nowhere-density bridge to close the non-Ramsey-null and open-not-Ramsey conclusions at the actual direct monoid neighborhood definition. This cannot be inferred from the already validated **fat-tree** Ellentuck theorem.

Do not confuse these obligations with the previously found fat-to-monoid projection counterexample, which refutes a **proof** but not by itself the Theorem 1.11 **statement**.

**Validation policy:** No `sorry`/new axioms; exact-name audit at each stage; do not change frozen manuscript prose. Do not call the complete Theorem 1.11 counterexample *Lean verified* until all six obligations have kernel proofs.
