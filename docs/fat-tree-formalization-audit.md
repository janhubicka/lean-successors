# Fat-tree formalization audit

This note records the proof obligations exposed while formalizing the fat-tree
part of the successor-tree manuscript.  It deliberately stops before the
optional embedding-space Ellentuck theorem.

## Scope

The formalization treats:

- finite and infinite fat trees, with finite trees carrying the terminal cut;
- canonical row extensions;
- the recursive Lift operation;
- infinite and finite fat-tree reduction;
- reflexivity and transitivity of reduction;
- the proposed finitary order for Todorčević A.2;
- the first finiteness ingredients for A.2(1).

The optional embedding Ellentuck axiom (EA) is not used in any of these
definitions or proofs.

## Changes forced by formalization

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

### 5. A.2 is not all immediate

The proposed finite relation

    x <=fin y  iff  x <= y and terminalCut(x) = terminalCut(y)

is a quasi-order.  Formalization also proves that the height of a finite fat
tree is bounded by its terminal cut.

The remaining finiteness clause A.2(1) should not be dismissed only by the
phrase “the tree is finitely branching”.  The proof needs an explicit finite
code: bounded one-row approximations are encoded by maps between finite
initial tree segments, and a finite fat tree is then encoded by finitely many
cuts and row codes.  This coding is the current formalization target.

A.2(2) and A.2(3) should receive separate proofs after A.2(1); they have not
yet been certified merely by the quasi-order proof.

## EA boundary

The updated manuscript's placement of (EA) is the correct one for this
formalization pass: it is an optional assumption for the full Ellentuck
theorem on shape-preserving embeddings.  It is not used by the fat-tree
Ramsey space, the finite-dimensional theorem, or the pointwise-Borel
embedding theorem.

## Validation convention

A green manuscript marker should be used only for statements which have
passed the Lean build and the axiom audit.  The A.2 paragraph remains partial
until the lower-finite and approximation clauses are formalized.
