# Independent B3 spacing and age-test statement audit

Proof candidate: `PrescribedB3Spacing.lean`, independent PR #197.
This note is review-only until its exact-head Lean build and axiom audit
pass; no mathematical manuscript proof prose is changed.

## First-upper spacing obstruction

A genuinely admissible Kpt node at level ell+1 has the auxiliary
E-relation from every ordinary socle coordinate j<=ell to its
distinguished type vertex t. In particular E(ell,t)=true.

An initially enumerated finite partial structure A instead has
E(ell,ell+1)=false, by the strict spacing condition u<v-1. Thus
the first vertex after ell cannot have its complete type through
ell+1 equal to ANY admissible Kpt node at level ell+1.

Therefore the manuscript B3 antecedent

  for every i>=ell+1, type_A^(ell+1)(i) lies in f[S]

cannot hold in any initial-ordinal partial structure having a
nonempty upper tail, when f[S] consists of admissible Kpt nodes.

## Empty-upper-tail counterexample

The same antecedent imposes no restriction when |A|=ell+1.
For ell=2, consider a 3-vertex partial structure whose only positive
directed L-relation is (0,2), with E(0,2) and no other E-pairs.
The E relation is spaced and downward-closed and witnesses the
single linked pair. For the forbidden family containing the
ordered directed edge, the copy on vertices (0,2) uses ell but
no forbidden copy avoids ell. Thus the printed B3 conclusion
fails, regardless of f, although the antecedent's upper-tail
condition holds vacuously.

## Shortest mathematically meaningful repair to consider

A finite ordered L-age-test rather than a finite E-expanded partial
structure: require the first ell+1 ordinary vertices to induce the
L-socle of some admissible prescribed output f(S). Each designated
later vertex must have exactly the COMPLETE induced L-type
through ell+1 of some f(T), including nonrelations, both binary
directions, unary and diagonal data. If the L-reduct after deleting
ell is F-free, the full ordered L-reduct must be F-free.

This is precisely the scope of the independently checked
CommonSocleAgeTest predicate. It is stronger than the printed
B3 and is not a consequence of it. The issue requires an editorial
decision; this patch only adds a TODO, not a replacement proof.

The neutral ShapeMap and previous four author proof repairs stay intact.
The original author-edited current main.tex is not available as
verified raw source here. The source updater still retains nine grouped
TODOs and modifies only its own machine-labelled notes.
