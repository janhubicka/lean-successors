# Local repair of the boring extension lemma (v10)

This patch changes the mathematical hypothesis and proof of the lemma
labelled \`lem:boring\` (or \`lem:local-age\` on branches that renamed it),
not merely the TODO overlay. Apply the accompanying strict source updater to
the author's *current* main.tex. No current TeX checkout is stored in
\`lean-successors\`, and no obsolete archival manuscript is overwritten.

## Why the original B3 was incorrect

The original condition said every upper vertex i >= ell+1 of an initially
enumerated partial structure A has its complete E-expanded type through
ell+1 in f[S]. At the first such vertex, E(ell,ell+1) is forbidden by the
spacing condition u<v-1. Any admissible type at level ell+1 instead has
E(ell,t). The antecedent therefore permits no upper vertex, and with
an empty upper tail it does not constrain the initial L-socle.
This is checked in the independent Lean module PrescribedB3Spacing
(PR #197), with both the focused axiom audit and full build passed.

## Minimal usable replacement

(B3) quantifies over finite *L*-structures on a finite ordered subset
of the naturals containing {0,...,ell}. The first ell+1 ordinary vertices
must have the same induced L-reduct as the ordinary part of some f(S0).
For every other vertex x, its FULL ordered L-type (including both
binary orientations, nonrelations, unary and diagonal data) through
that socle must be the L-reduct of some f(Sx). If an F-copy occurs,
another must occur avoiding ell. No auxiliary E is imposed on this
auxiliary age-test structure.

This is the geometric CommonSocleAgeTest hypothesis already used by
the finite Lean modules LocalAgeForbiddenTest and PrescribedB3Finite.

## Proof repair and remaining certification

A forbidden copy in the newly inserted Q either avoids ell and projects
to T, or contains ell. The mismatched-socle branch inserts an L-isolated
neutral vertex and cannot contain an irreducible forbidden copy.
For the matched branch, restrict the forbidden copy to the common first
ell+1 L-socle and its upper members. Irreducibility makes each upper
member linked to ell, and the prescribed upper columns give its complete
L-type f(S). Deleting ell pulls back to the source T. Corrected (B3)
now yields the contradiction.

At the crossing successor step n=ell-1, the ORIGINAL successor is
only a prefix of its image; equality is false and is no longer asserted.
For n>=ell, exact commutation needs the separately checked parameter
and terminal-letter transport. A second indexing error
"type_Q^ell(i+1)=F(S)" is corrected to ell+1.

### Downstream effect (not hidden)

The old Lemma comp only discussed a complete E-expanded upper-tail test.
It does **not** establish the strengthened finite common-socle L-age test.
Consequently, the proof of decomposition/M2 referring to it still has an
explicit TODO. The blanket claim that the boring lemma's assumptions are
necessary also needs independent reconsideration. Do not mark the global
(S,M)-tree axioms, M2/M3, or the final big-Ramsey application GREEN merely
because the finite insertion is checked.

The replacement is source-targeted and fail-closed: only B3, its age
argument, the weak successor paragraph, one adjacent index, and the
downstream application sentence are modified. Preserve prior four
author-approved repairs.
