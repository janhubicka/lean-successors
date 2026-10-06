# Fat-tree formalization audit

This note records the proof obligations exposed while formalizing the fat-tree
part of the successor-tree manuscript.  It deliberately stops before the
optional embedding-space Ellentuck theorem.

## Scope

The formalization treats:

- finite and infinite fat trees, with finite trees carrying the terminal cut;
- the A.1 sequencing axioms through a typed exact-approximation interface;
- canonical row extensions;
- the recursive Lift operation;
- infinite and finite fat-tree reduction;
- reflexivity and transitivity of reduction;
- the proposed finitary order for Todorčević A.2;
- all three A.2 clauses, including explicit lower-cone finiteness and the
  converse finite-approximation characterization;
- the finite-prefix splice construction used in the manuscript's A.3 proof;
- both A.3 amalgamation clauses in basic-neighbourhood form.

The optional embedding Ellentuck axiom (EA) is not used in any of these
definitions or proofs.

## Changes forced by formalization

### 0. A.1 is elementary but not definitionally trivial

All three A.1 sequencing clauses are now Lean-checked.  The only formal
subtlety is that finite fat trees have dependent cut and row fields: equality
of two finite approximations cannot be reduced to an untyped sequence
equality without transporting those dependent indices.  The proof therefore
uses explicit pointwise/heterogeneous extensionality.  This introduces no new
mathematical hypothesis.

Actions run 37188688958 checked the A.1 sequencing theorems using only
propext, Classical.choice and Quot.sound, with no sorryAx.

### 1. Canonical extension in Lift

A row of a fat tree is a finite approximation.  In the definition of Lift,
the notation u_i^+ must mean the canonical extension of that finite row.
An arbitrary total representative is insufficient for the displayed
next-cut calculation.

### 2. Subtraction-free cut equation

The row condition can equivalently be written

    rowEndLevel(u_i) + 1 = c(i+1).

This makes strict growth and injectivity of the cut a derived theorem.  It is
not a new hypothesis.

### 3. Source locality of Lift

The transitivity proof needs more than monotonicity.  A node in
Lift_U(X,k) remembers its unique ancestor on the starting cut.  Hence a
full-level lift inclusion restricts to every subset of the source level.

With this lemma, the reduction relation in the manuscript is transitive as
stated.  No strengthening of the definition is needed.

### 4. Terminal cuts in finite reductions

For a finite fat tree of height q the cut map has q+1 values.  A finite
reduction witness is therefore a strictly increasing map on all q+1 cuts.
The terminal-cut clause in the manuscript is essential and is preserved
automatically when reduction witnesses are composed.

### 5. A.2 needs real proofs, and they are now checked

The proposed finite relation

    x <=fin y  iff  x <= y and terminalCut(x) = terminalCut(y)

is a quasi-order, and all three A.2 clauses are now Lean-checked and included
in the axiom audit.

For A.2(1), fixing the terminal cut d bounds the height by d.  A one-row
approximation ending below d is encoded by its map between finite initial
segments of T.  Padding these row codes gives a single finite ambient code
space for all finite fat trees ending at d.  This proves lower-cone finiteness.

For the converse in A.2(2), the finite witnesses do not merely "follow from
the definition".  Equality of terminal cuts identifies their target indices;
injectivity of the ambient cut function forces these indices to be coherent.
The coherent indices and one-block inclusions then assemble into a single
infinite reduction witness.

A.2(3) is proved by restricting a finite reduction witness to the requested
initial segment; keeping the terminal cut in the finite witness is precisely
what makes this restriction land in <=fin.

Actions run 37181899053 checked these A.2 theorems together with the preceding
fat-tree structural results.  All fourteen axiom reports used only propext,
Classical.choice and Quot.sound, with no sorryAx.

### 6. A.3 is checked

The manuscript proves A.3 by concatenating a finite stem with an infinite
tail.  This construction is represented explicitly by `FatTree.splice`.
Its terminal-cut compatibility is the only structural hypothesis, and the
construction uses no EA assumption.

A.3(1) is `a3_one_nonempty`: if `x` has depth `n` in `U`, every
member of `[n,U]` admits the splice of `x` to its tail, producing a member
of the required basic neighbourhood.

A.3(2) is `a3_two_amalgamation`: for `V <= U` with nonempty `[x,V]`,
the construction splices `U|m` to the tail of `V` at the common terminal
cut and proves the resulting `U'` lies in `[m,U]`; every member of
`[x,U']` is then rebased into `V`.  Thus the checked conclusion is the
textbook inclusion `[x,U'] subseteq [x,V]`.

The manuscript currently states the stronger equality of these two
neighbourhoods.  That equality is unnecessary for A.3 and is not part of the
formalized theorem, so the manuscript should either weaken this sentence to
the required inclusion or supply a separate reverse-inclusion proof.

Actions run 37187320737 checked seven A.3 reports, including both final
clauses, using only the standard Lean axioms and no `sorryAx`.

## A.4 status

A.4 is the remaining fat-tree Ramsey-space axiom.  The finite bridge and
complete finite-prefix trace update are now checked.  Exact trace families are
finite; appending one row satisfies the exact Lift recursion; raw successor
tables yield exact appended traces; and the converse direction is obtained by
shape-splitting an arbitrary exact appended trace back to the old terminal
cut.  Thus the manuscript identity Q_{y⌢h}=Q_y[h] is now formalized in both
directions without assuming an admissible extension of the raw table.

Actions run 37197761609 checked eight A4 bridge/trace reports using only
propext, Classical.choice and Quot.sound, with no sorryAx.

The remaining A4 work is the simultaneous finite successor-fan profile
stabilisation, persistence of large trace families, and the final all-trace
fusion covering every geometric one-block reduction.  Until those are green,
A4 itself remains partial.

## EA boundary

The updated manuscript's placement of (EA) is the correct one for this
formalization pass: it is an optional assumption for the full Ellentuck
theorem on shape-preserving embeddings.  It is not used by the fat-tree
Ramsey space, the finite-dimensional theorem, or the pointwise-Borel
embedding theorem.

## Validation convention

A green manuscript marker should be used only for statements which have
passed the Lean build and the axiom audit.  A.2 and A.3 now qualify.
