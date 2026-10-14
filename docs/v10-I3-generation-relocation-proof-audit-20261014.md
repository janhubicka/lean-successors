# V10 Lemma 6.53 — relocation-to-age-witness bridge

**Status: mathematical proof checked at paper level; Lean endpoint not yet complete.**
**Scope: the fixed binary/unary/diagonal normalized language and the
existing successor axioms.** The author manuscript remains frozen.

## Data already available

Let (C^+) be the exact H-construction, and let (ell>0) be
selected by I3. The corrected finite B3 test fails for the
prescribed ambient-original source map (f_ell).

`I3AgeFailure.lean` gives a finite ordered L-witness (W)
whose initial socle through (ell) agrees with (C^+),
whose deletion (W\setminus\{\ell\}) omits all forbidden patterns,
and which contains an ordered induced forbidden copy (e:F\to W).
The tested coordinate (ell) necessarily belongs to that copy.

`I3PrescribedOriginalWitness.lean` shows that if the sources
of (f_ell) arise from one ambient partial structure, its
unqualified corrected B3 test equals the compatible B3 test.
A failed test then gives ambient originals for all upper vertices
without extending W by E.

`I3AmbientPrescribedPool.lean` constructs a canonical B1/B2 map
from a finite list of ambient originals: old prefixes at cut (ell)
are sources, and each complete target prefix is chosen from the
SAME original at cut (ell+1). Duplicate old types are resolved by
a representative, and both B1 and B2 are direct calculations.
This is a model for the manuscript's I3 function; literal identity
with the author's (f_ell) must be checked before using the result.

## Proof of the generation conclusion

Write the vertices of (e[F]) at or below (ell) in order as
[
    \iota(j_0,n_0)<\cdots<\iota(j_{r-1},n_{r-1})=ell.
]
There is at least one and at least one upper vertex:
(1\le r<|F|\le k). The lower part of the forbidden copy is
irreducible. The exact H construction then makes all its vertices
real, with strictly increasing first indices (j_a). The linked
generation-gate theorem gives (a\le n_a) for each (a<r);
in particular (r-1\le n_{r-1}).

Assume (n_{r-1}>r-1). Replace each lower vertex
(\iota(j_a,n_a)) by (\iota(j_a,a)), leaving the upper
witness vertices fixed. The relocated lower vertices are all
strictly before (ell). The complete induced copy can be checked
in four zones:

1. **Lower–lower.** The old and relocated pairs are linked real
   H pairs. Both permitted generation gates copy exactly the same
   base relations, in both directions and including missing tuples.
   Unary and diagonal singleton facts also agree.
2. **Lower–upper.** Let (v_b=\iota(j_b,n_b)) be the
   ambient original naming an upper vertex of W.
   The prescribed full L-type through (ell+1) implies that
   its relation to each lower socle vertex equals its relation
   to (v_b) in (C^+). Irreducibility forces the old lower–
   upper pair to be linked. Thus (j_a<j_b) and the old gate is
   (n_a<n_b), or the exceptional top tie (n_a=n_b=k).
   The rank estimate (a\le n_a) and (a<k) imply (a<n_b).
   Hence the relocated pair is allowed and carries exactly the
   same base relation, in both orientations, true and false.
   The full original type also supplies all upper unary/diagonal
   facts.
3. **Upper–upper.** No upper vertex is moved, so every atom is
   literally unchanged. Do **not** replace these pairs by nonedges.
4. **Order/carrier.** The relocated lower vertices remain
   increasing and precede every upper vertex. All are in the
   initial socle of W; the original upper vertices remain
   in W. Since (n_{r-1}>r-1), none of the relocated vertices
   equals (ell).

The result is an induced ordered copy of F inside
(W\setminus\{\ell\}), contradicting its forbidden-free age.
Therefore (n_{r-1}=r-1<k). Finally each upper vertex is
linked to (ell), and the exceptional top-tie gate is now
impossible. Its named original must have generation strictly
greater than (r-1), as required by Lemma 6.53.

## Exact Lean bridge still needed

The following are already kernel-checked independently:

- `HGenerationRank.lean`: linked-gate and rank lower bound
- `RelocationIrreducible.lean`: all mixed directed binary atoms
- `RelocationOrder.lean`: relocated order and avoidance of (ell)
- `RelocationCopy.lean`: unary, diagonal and upper–upper retention
- `ActualCrossingSignature.lean`: actual Kpt crossing equals
  the ambient original's complete L-prefix

The missing theorem should take an actual (W), ordered forbidden
copy (e), original labels for its upper vertices, the exact H
representation of the lower part, and the common initial socle.
It must assemble the four zones into a single
`AgeTestModel.Realizes` for the relocated copy, and use the
verified deletion avoidance to force (n_{r-1}=r-1).
Only afterwards derive the strict generation increase of
all non-bottom signature originals.

Do not turn any of those conclusions into new assumptions
inside the final upper-bound theorem. This bridge is what links
the already formalized finite signature counting to the
actual I3-selected generation levels.
