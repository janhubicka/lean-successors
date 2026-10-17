# Empty-language Kpt versus the free ancestral successor tree

Status: draft PR #570, **formalization in progress**. Do not claim a Kpt
Ellentuck counterexample until the stated monoid/topology transport is checked.

## Finite coding

For the empty (L) and forbidden family, all ordinary positive (L)
atoms vanish. At cut (ell=n+1), write (d_j) for the free cut of ordinary
vertex (j), (0\le j\le n). The (E)-axioms force

```text
d_0 = 0,
d_{i+1} = 0 or k+1 for one k < i.
E(u,j) iff u < d_j.
```

A one-letter free history of length (n), with at most one ancestral
parameter per successor, makes exactly the same choices. The translation
is `emptyPartialType (toCutHistory h)`. Its full distinguished-type
(E)-column has every (E(i,t)), (i< n+1); it has no reverse (E)
entries. There are no (L) facts.

The admissibility witness is a finite structure on (n+3) vertices:
retain all encoded ordinary columns on (0,\dots,n), put a neutral
spacer at (n+1), and place a type vertex at (n+2) whose (E)-cut
is (n+1). Thus (E(i,n+2)) holds exactly for (i<n+1).
The spacer is **necessary** for the spacing axiom.

## Lean modules

* `EmptyKptCutHistory`: parameter cuts and exact coding bijection
  with `FreeAncestral.History Unit 1`.
* `EmptyKptPartialType`: full empty-(L) partial-type record and
  proofs of ordinary (E)-spacing and downward closure.
* `EmptyKptAdmissible`: constructs an actual finite admissible
  partial structure and extracts precisely the encoded record.

The third layer is not the converse. The following remain to formalize:

1. **Exhaustiveness.** Every node of
   `admissibleKptSTree ([] : List (NormalizedForbidden 0 0 0))`
   at positive level is one encoded cut history, uniquely.
   Use the admissibility witness to reconstruct each finite
   (E)-column, and prove that all (L) data are empty.
2. **Successor correspondence.** At source level (n+1), the new
   ordinary vertex has cut (0) (empty parameter) or cut (k+1)
   (the **ancestor Kpt node at level (k+1)**). The terminal
   letter is unique. This must be an equivalence of actual
   `S.succ` graphs, not merely level counts or order.
3. **Extra root.** Kpt has an additional level-zero root. Its
   unique level-one child corresponds to the free-ancestral
   history root. Maps in `KptM` fix the extra root but are free
   to move the level-one child upward. This matches the
   unrestricted free-ancestral monoid.
4. **Shape maps.** Use the successor equivalence, injectivity,
   root extension and the strict level law to transport a
   shape map in either direction. Check identity, composition,
   `SkipsOnly`, and the exact finite-approximation cutoff.
5. **Topology.** Show algebraic right reduction, finite stems,
   their depth-preserving pure refinements and the monoid Ellentuck
   topologies correspond. The source levels shift by **one**:
   free root level (0) corresponds to Kpt level (1).
   A bare order-tree isomorphism does not prove this.
6. **Obstruction.** Transport the Lean-verified
   `Counterexample.exists_meagre_not_avoidable` through
   the monoid/topological isomorphism. Deduce that EA1+EA2,
   considered jointly as sufficient conditions for the
   manuscript's depth-preserving Ellentuck theorem, do not
   follow from (M1)–(M3) for all Kpt forbidden families.

## Adversarial checks

* Do not identify a partial-type parameter with the last new ordinary
  vertex. Its positive free cut (k+1) prescribes the **prefix
  at level (k+1)** of the current type, exactly the shifted
  ancestor of the free history.
* Ordinary E-relations are copied in **both** directions; the reverse
  direction is forced false by spacing. The type vertex's incoming
  E-column is full, independently of the ordinary cut history.
* No forbidden (L)-relations are created: the language is empty.
  Consequently the construction does not establish an analogous
  retraction for an arbitrary nonempty forbidden family.
* Meagreness and Ramsey-nullity must be transported in the actual
  **right-composition** Ellentuck topology, not simply the pointwise
  topology or the fat-tree topology.
* The counterexample proves only that EA1 and EA2 **cannot both hold**
  in this specialization. It does not isolate a failing clause.

## Applications after the correspondence

1. The unconditional finite shape-preserving Ramsey theorem and the
   big-Ramsey-degree application remain valid: neither uses EA1 or EA2.
2. The v18 pointwise-Borel theorem for *fat-image* colourings is not
   contradicted by a non-Ramsey direct composition cone.
3. For classes with a nontrivial forbidden signature, merely containing
   an E-only neutral subforest is insufficient to transfer the
   negative conclusion. A monoid retract/topological lifting is needed.
4. The one-letter **parameter-free** successor chain is a natural
   positive comparison: its right-composition order resembles the
   classical Ellentuck space on infinite subsets of \(\omega\).
   This remains a candidate; no EA1/EA2 verification is claimed.

The last three items distinguish existing proved consequences from
genuinely new application problems.
