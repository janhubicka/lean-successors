# Theorem 1.11: checked counterexample, and the surviving fat-tree theorem

**Status (17 October 2026): REFUTED under the manuscript's original M1–M3 assumptions and depth-preserving pure-refinement definition.** The construction is now **proved in Lean**, rather than only an English counterexample or a gap in the fat-tree transfer proof.

The example is the already verified full shape-preserving monoid of the free-ancestral history tree with one label and one ancestral parameter. The *same* concrete tree satisfies M1–M3. It has a finite root approximation `f(root)=s` of depth 1 (level convention) such that a set `Z` can be:

- **closed nowhere dense** in the genuine **monoid Ellentuck topology** defined from right-composition basic neighbourhoods;
- **meagre** in that topology;
- nevertheless **unavoidable** by every pure `H∈[1,Id]`: `[f,H]∩Z ≠ ∅`.

Thus the manuscript's unqualified claim that every Ellentuck-meagre monoid set is *Ramsey null under depth-preserving pure refinements* is false. Its open dense complement is not Ramsey for the same pure-refinement definition.

## Exact Lean theorems

* `SuccessorTree.FreeAncestral.freeSMTree` — the underlying free-ancestral instance has M1–M3 (unchanged).
* `SuccessorTree.FreeAncestral.markedFusion` — total shape maps `Q_A`, constructed by *verified one-gap maps and pointwise M1 fusion*, not an unproved raw-history assertion.
* `SuccessorTree.FreeAncestral.compatible_marked_has_infinite_support` — the **key lemma**: a common algebraic right multiple of `G` and `H ∘ Q_A` gives a fixed infinite meeting-level witness set contained in A, when `G(root)` lies above the root and `H(root)=root`.
* `SuccessorTree.Counterexample.branchLevel_almostDisjoint` — explicit continuum-sized family of pairwise almost-disjoint retained-level sets, indexed by infinite binary sequences.
* `SuccessorTree.Counterexample.greedySelection` and `exists_pure_meeting_incompatible_family` — a ZFC well-founded greedy recursion selects a pairwise right-incompatible family N meeting *every* pure right-composition cone. Proper initial segments of the minimal continuum well-order are smaller regardless of CH or regularity of continuum.
* `SuccessorTree.SMTree.incompatible_family_isNowhereDense` — a generic theorem: a pairwise right-incompatible family is nowhere dense when sufficiently late proper gaps exist. This is proved for the **actual direct monoid topology**, not a fat-tree substitute.
* `SuccessorTree.Counterexample.exists_closed_nowhereDense_not_avoidable` — the original counterexample as an exact topological Lean theorem, taking `Z = closure N`.
* `SuccessorTree.Counterexample.exists_meagre_not_avoidable` — literal meagre-but-not-pure-Ramsey-null corollary, exported from `SuccessorTree.Library.Examples`.

All the principal endpoint lemmas have exact-name **transitive-axiom checks**, and the focused CI forbids sorry/admit/new mathematical axioms. The full counterexample passed [the focused proof CI](https://github.com/janhubicka/lean-successors/actions/runs/38986241498) and was merged in [PR #565](https://github.com/janhubicka/lean-successors/pull/565).

## A crucial distinction between Ramsey definitions

The manuscript's **depth-preserving** definition requires a refinement `H ∈ [depth_F(f),F]` keeping the original depth. For `f(root)=s`, this is exactly the pure family `[1,Id]`, meaning `H` fixes source levels **0 and 1**. The abstract approximation-space index for this level neighbourhood is **2**, not 1.

The weaker **textbook/basic-neighbourhood** convention permits the finite stem itself to be end-extended and allows any refinement `B ∈ [f,F]`. Without direct A.3(2), the two conventions need not coincide; **this counterexample is expressly about the manuscript's depth-preserving convention**. It must not be presented as a refutation of every textbook variant. The Lean endpoint `AvoidableAtRoot` records the exact quantified pure-refinement property, rather than silently using a stronger/unavailable A.3(2) equivalence.

## Original Section 4 projection issue remains independently real

The original proof of Theorem 1.11 attempted to transfer the checked fat-tree Ellentuck theorem by projecting fat trees to shape maps. That transfer requires a projected-neighbourhood identity `π([x,U])=[F_x,F_U]`. The free-ancestral E₀/E₂ algebraic witness already shows that even the claimed forward inclusion fails; the delayed witnesses expose a discontinuity in the relevant Ellentuck topologies. Those facts originally showed **a faulty proof**, not a false statement. The new, separate **fully formalized** nowhere-dense construction establishes that the *statement itself* fails.

## What remains correct

- **Theorem 1.17 (fat-tree Ellentuck): CHECKED**. Fat trees satisfy the relevant A.3(2); the counterexample does not affect them.
- **Theorem 1.6 (finite shape Ramsey): CHECKED** via two independent routes, including the fat-tree Ellentuck route. The construction does not give a bad finite colouring.
- **Direct monoid A.1/A.2/A.3(1), finite neighbourhood nonemptiness and Tychonoff closedness: CHECKED**; A.3(2) is deliberately **not** claimed.
- The unconditional **pointwise-Borel fat-image Ramsey theorem** described in the separate English Section 4 note remains a valid weaker positive statement. It is **not** a monoid-neighbourhood Ramsey theorem.

## Manuscript review policy

The author-edited v10 manuscript is frozen. Do not rewrite Theorem 1.11 or Section 4 automatically. Record the refutation in **TODO/validation markers**, propose a localized correction to the authors, and separately audit any downstream use of the shape-map *topological* theorem. The validated finite shape-Ramsey, fat-tree Ellentuck and final finite big-Ramsey arguments should retain their independent verification markers.

The standalone [English counterexample](../theorem111-zfc-counterexample-20261016.md), [adversarial audit](../theorem111-zfc-counterexample-referee-20261016.md), and [Lean validation progress](../theorem111-counterexample-lean-progress-20261017.md) give the full mathematical and formal proof record.
