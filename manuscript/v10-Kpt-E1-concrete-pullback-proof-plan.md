# V10 concrete Kpt one-level pullback (E1): detailed construction and adversarial checkpoints

15 October 2026. Review-only source kept in Git; **not** a green Lean certificate.
Do not change the author's circulation prose or silently add E1 to the final theorem.

## Precise target

Let H = normalizedKptSMTree family and F be a genuine member of its monoid
(indeed the argument is expected to work for an arbitrary genuine Kpt
ShapeMap, not just one skipping a single level). Let a be a genuine
admissible Kpt node of level n, p a finite list of genuine admissible
parameter types and c an admissible terminal Sigma letter. Suppose

    (admissibleKptSTree family).Defined (F a) (p.map F) c.

Choose the genuine target successor b+ and the unique target one-step
complete record Q+ at level lambda(n)+1. We must construct a real
source successor b satisfying

    (admissibleKptSTree family).Defined a p c.

This is the missing Section 5 OneLevelPullback/E1 statement needed by
the unconditional proof of Theorem 6.26. It does NOT follow abstractly
from M1–M3 (see Example 5.6), and must be proved from the finite Kpt
records and their hereditary forbidden-L age.

## Concrete source record

The genuine shape map F has a strictly increasing common level map
lambda. For each original source coordinate i<=n, retain the target
coordinate lambda(i) in the complete record Q+. Define the source
PartialTypeWithE Q at level n+1 by pulling back BOTH L and E on

    rho : Fin (n+1) -> Fin (lambda(n)+1),  rho(i)=lambda(i),

and sending the distinguished type vertex 'none' to 'none'.
No additional image coordinate is kept. The terminal L+ letter is
therefore literally c: new ordinary coordinate n corresponds to
lambda(n), the target's last ordinary coordinate.

The old restriction Q|n equals a's complete record by the
verified shapeMap_recovers_complete_record on a and the fact that
the target successor's predecessor is exactly F(a).

## Canonical successor parameter

The target canonical successor has either an empty parameter list
or one parameter F(p0) of level f'=lambda(f), where f=level(p0).
This follows from the already proved unique canonical decomposition
of successor inputs and the literal equality p.map F. Since F
is injective, source p is respectively empty or [p0]. In the
positive case, f>0 and f<n follows from strictness of lambda and
the canonical target cut condition f'<lambda(n).

The target new ordinary E-column is true precisely below f'.
Its restriction to retained coordinates satisfies

    E_Q(i,n)=true iff lambda(i)<f'=lambda(f) iff i<f.

For the empty parameter case the E-column is empty and f=0.
The resulting source parameter is precisely p, not merely
isomorphic to it: the pulled-back L+ new-ordinary type at level f
is the fully retained record of F(p0), hence equals p0 by
shapeMap_recovers_complete_record on p0.

Because f<n, the source new-ordinary column is spaced.
All old E-columns are the legitimate old source a record. Linked
binary pairs imply the E incidence by the target linked_E
axiom and the strict level cut. The E3 no-new-tuples law is
inherited at the retained source coordinates. Thus Q satisfies
all canonical successor-record constraints.

## Forbidden L-age and actual admissibility

The **forbidden age is an L-test**, with no auxiliary E imposed on
its witnesses. The new theorem
PartialTypeWithE.reindexOrdinary_age_avoids in PR #517
proves that the complete L-age model of Q embeds inducedly and
in increasing order into the legitimate target Q+ age model,
by i↦lambda(i) and type-vertex↦type-vertex. Hence Q has forbidden-free
L-age, preserving BOTH orientations and absence of binary tuples,
unary and diagonal facts.

This alone is NOT an admissibility certificate for Kpt.
Construct an actual finite L+ partial structure W of size n+3:
ordinary vertices 0,...,n retain the whole induced type Q; vertex
n+1 is a neutral spacer; type witness vertex n+2 carries the
distinguished type L-data. Assign free E-columns from their
proven cuts: old vertices use the E-record of a; new ordinary n
has cut f; neutral spacer n+1 has cut 0; final witness n+2 has
cut n+1. This makes E downward-closed. Spacing holds for all
columns, crucially at the new ordinary since f<n and at the
type witness since the neutral spacer separates n from n+2.
The linked_E property follows from the pulled-back new column,
old a, and full type E-socle. Neutral filling preserves the
forbidden L-age (use the checked M2NeutralCarrierFill /
M2SparsePullbackAge lemmas).

Prove fl_W(n+2)=n+1 and
W.partialTypeAt(n+1,n+2)=Q **literally**. This witnesses
IsAdmissibleRawType family ⟨n+1,Q⟩, not just L-age avoidance.
Then the checked canonical step graph makes
IsCanonicalKptStep family a p c b, and
canonicalKptSucc_eq_some_of_step gives the genuine source
successor. Abstract the result into

    normalizedKpt_oneLevelPullback :
      SMTree.Envelope.OneLevelPullback (normalizedKptSMTree family).

## Adversarial checks before marking E1 green

1. Never use a freely chosen E-expansion of an L-only forbidden witness.
2. Retained coordinates must be bounded by the target successor level;
   prove rho strict and all dependent Fin casts explicitly.
3. Verify the new ordinary's **actual** free cut equals f, not merely
   the implication E(i,n)→i<f.
4. The empty parameter case must remain separate from f>0.
5. Verify BOTH binary directions, their absences, all unary and
   diagonal facts and E including the reverse and diagonal bits.
6. Source old E-columns must match the original a witness; generic
   monotone reindexing alone does NOT preserve E spacing when
   source-consecutive coordinates map far apart.
7. The dummy spacer n+1 is essential: without it the final type
   witness would have forbidden consecutive E(n,n+1)=true.
8. Check actual full source admissibility with freeLevel=n+1 and
   literal extracted record, not merely an L-age theorem.
9. Once E1 is green, instantiate the existing AlgorithmRun E1-dependent
   coverage, sharp uniform selected-level bound, bounded G+ source
   palette, the simultaneous finite-colour theorem, and the ordered
   K→H+→Gω→K transfer. The latter remains unverified until an actual
   Lean theorem has all hypotheses discharged.

**Status:** Detailed constructive English argument and proof plan;
only the explicitly named prior endpoints carry their own individual
Lean-green certificates. Do not report Theorem 6.26 complete yet.
