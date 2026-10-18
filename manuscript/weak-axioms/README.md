# Ramsey-first manuscript branch

This directory stores the experimental manuscript changes; it is not a replacement for main and must not be merged with the weak global Ramsey theorem still unresolved.

## Exact patch base and order

Base source archive: `successor-v20-compact-axioms-sources.tgz`.

SHA-256: `83faf741dec0ff77b25fd1dbd4125bb2af238573e5c8ba96c438a72855aa207a`.

Apply inside the extracted `successor-clean/` directory, in this order:

1. `ramsey-first.patch`: literal weak/strong terminology, finite-profile lemma, conditional bounded-family lemma, exact-core interface markers, explicit strong scope of the established unrestricted results and the envelope section.
2. `ramsey-first-widening.patch`: replace the legacy strong internal-cut proof of map-to-fat widening by a direct weak-axiom proof.

The conversation deliverable `successor-v20-weak-ramsey-first.patch` combines these two patches against the exact base. Apply either the series or the combined patch, not both. Both routes are checked by zero-fuzz replay and byte comparison.

M1 and the full primed-axiom definition remain verbatim. Appendix A and application constructions are unchanged. The envelope section gains only explicit strong scope; its algorithm is not altered.

## Additional weak result: map-to-fat widening

For an admissible map F, write f_i for its restriction through source level i. Set u_0=f_0. For i>0 the new M3 supplies D_i with

    f_i^+ = D_i composed with f_(i-1)^+.

Put p=F~(i-1), q=F~(i). The already proved normalisation forces D_i to fix all levels through p, map p+1 to q, and continue consecutively thereafter. Hence its restriction u_i through p+1 is a legal old-convention fat row and u_i^+=D_i. The fat cuts are

    cut(0)=0, cut(i+1)=F~(i)+1,

and the row-completion product through i is exactly f_i^+. Its pointwise limit is F. The root seed need not be fixed. This proves the existing map-to-fat surjectivity statement from the weak completion/factorisation/fusion package; neither arbitrary internal cuts nor duplication are used.

This is an English proof, not a newly compiled weak-record constructor. Its previous strong green marker is replaced by an interface marker. It does not prove that geometric reduction projects to algebraic right factorisation, and does not prove A4.

## Checked versus pending

The generic M4 Ramsey core is kernel-checked at `70ae3b4e71de18d16dae2276a389574fc05da7d9`, focused run `39128732027`. All seven named reports passed. See `docs/weak-axioms-ramsey-first-20261018.md` for exact scope and audit evidence.

Next: relative whole-frontier representation in finite boundary batches, common-base/colour compatibility, persistence, and fusion covering every extension. Finite profile homogeneity is not by itself homogeneity of an infinite A4 front. The genuine parity-monoid counterexample prevents silently dropping these issues from the unrestricted shape theorem. No new axiom is being inserted here to restate the desired conclusion.
