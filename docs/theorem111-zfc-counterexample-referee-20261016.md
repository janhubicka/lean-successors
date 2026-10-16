# Theorem 1.11: adversarial audit of the ZFC counterexample

**Date:** 2026-10-16. **Target:** Theorem 1.11 of the successor-tree
manuscript, *not* the already disproved Lemma 4.1. Companion proof:
[the counterexample construction](theorem111-zfc-counterexample-20261016.md).

This is an independent-check **method** consisting of four proof
passes, not four external human referees and not a Lean proof.

## Verdict

**English proof: accepted after the checks below, with the stated
model and topology.** The incompatibility family and transfinite
nowhere-dense argument constitute a genuine ZFC counterexample
*if* the explicit mask map \(Q_A\) is verified to be a full
shape-preserving self-embedding. The required verification is
elementary and spelled out below; the finite code calculations
were independently exercised on source histories up to level 5,
including compositions of pure gap maps. There is **not yet**
a Lean formalization of \(Q_A\), the full compatibility lemma,
or the transfinite construction.

No additional axiom such as CH, Martin's axiom or regularity of
\(2^{\aleph_0}\) is used.

### Referee I: is \(Q_A\) genuinely a shape map?

The source free-ancestral tree uses an \(n\)-step history whose
new code is either empty or a *single ancestral parameter level*
\(k<n\). Let \(L=\{1\}\cup A=\{\ell_n:n<\omega\}\) strictly
increasing. The recursive \(Q_A\) prepends the empty root step,
copies the source child code \(c_n\) to the first child after
target level \(\ell_n\) (replace \(k\) by \(\ell_k\)), and
fills the remaining \(\ell_{n+1}-\ell_n-1\) child steps by
the root parameter \(0\).

This is a total map on **all** histories, not a partial map.
Its range levels are exactly \(L\). A source node at level \(n\)
maps to one at level \(\ell_n\), so source-level equality is
preserved. If two distinct source histories first differ in
their code at source step \(i\), their target histories first
differ at target step \(\ell_i\), since \(k\mapsto\ell_k\)
is injective and the empty code remains empty. Hence \(Q_A\)
is injective.

For \(h^\frown c\), its first target successor above \(Q_A(h)\)
has code \(\widehat c\). When \(c=(k)\), its parameter is
the image \(Q_A(h|_k)\), which is the ancestor of \(Q_A(h)\)
at target level \(\ell_k\). Thus the target \(\mathcal S\)
successor exists and is a prefix of \(Q_A(h^\frown c)\).
This is precisely the **weak** successor clause of
`ShapeMap`, not a stronger false immediate-edge condition.
The root maps to its child \(s\), so the root inequality holds.

**Disposition:** a bona fide member of the all-shape-map monoid.
The target code \((0)\) is legal at every filled step
since target level is at least 2. The mandatory step at the
retained target level uses an empty code or \((\ell_k)\)
with \(\ell_k\ge1\), never \((0)\).

### Referee II: compatibility lemma and quantifiers

The critical statement is:

\[
G(r)=s,\quad H|_{T^{\le1}}=\mathrm{Id},
\quad G\circ R=H\circ Q_A\circ S
\quad\Longrightarrow\quad
D_G^H=\{j\ge2:\lambda_H(j)\in\lambda_G[\omega]\}
       \text{ is infinite and contained in }A.
\]

- **Infinitude.** The strictly increasing level map
  of the common right multiple is unbounded and its image
  lies in \(\lambda_G[\omega]\cap\lambda_H[\omega]\).
  Since \(\lambda_H\) is injective, its preimage is infinite;
  removing 0 and 1 cannot destroy infinitude.
- **No marker at a \(G\)-retained level.** For any source
  \(k\), the next edge after a target node at level
  \(\lambda_G(k)\) on the image of a sufficiently long
  \(G\)-history is forced by the source successor's
  image parameter list. Every such parameter is
  some \(G(p)\), and \(\operatorname{lev}G(p)\ge
  \operatorname{lev}G(r)=1\). Hence this next edge
  is never labelled with the root parameter \(r\).
- **Marker after a skipped \(Q_A\)-level.** For
  \(j\notin A\), \(j\ge2\), the edge leaving level \(j\)
  in every sufficiently long \(Q_A\)-history uses
  parameter \(r\). Applying pure \(H\) preserves
  the mandatory *first* successor edge at level
  \(\lambda_H(j)\) with parameter \(H(r)=r\).
- **Quantifier match.** If \(j\in D_G^H\setminus A\),
  write \(t=\lambda_G(k)=\lambda_H(j)\).
  Take a **single** sufficiently long history of the
  common right multiple. Its two decompositions have
  exactly the same history at level \(t+1\). One
  representation forces root parameter 0 at that
  step, the other forbids it. This is a contradiction
  in the actual full-history tree, not merely a
  discrepancy in level ranges.

The condition \(G(r)=s\) is essential and is satisfied
at **every** stage of the transfinite construction:
each selected map has form \(H_\alpha Q_{A_\xi}\),
the pure \(H_\alpha\) fixes \(s\), and \(Q_A(r)=s\).

**Disposition:** the earlier possible mistake
"compatibility implies the level intersection is infinite"
is not being used as a false converse. The code marker
forces the *stronger* \(D_G^H\subseteq A\).
Consequently a fixed \(G\) and fixed \(H\) can be
compatible with **at most one** index in a pairwise
almost-disjoint family. This is the pivotal lemma.

### Referee III: topology and nowhere density

Let \(\mathcal N\) be pairwise incompatible under common
right multiples. For a nonempty monoid-basic
\([g,F]\), if it meets \(\mathcal N\) pick
\(K\in[g,F]\cap\mathcal N\), and choose a
non-surjective one-gap map \(D\) fixing the finite
source domain of \(g\). Then

\[
\emptyset\ne[g,KD]\subseteq[g,F],\quad
[g,KD]\cap\mathcal N=\emptyset.
\]

The inclusion follows from the *algebraic* factorization
\(K=FR\), so \(KD=FRD\).
If \(J\in[g,KD]\cap\mathcal N\), then
\(J=KDR\), a common right multiple of \(J\)
and \(K\); incompatibility gives \(J=K\).
Injectivity of \(K\) then forces \(\mathrm{Id}=DR\),
impossible since \(D\) omits an entire target level.
Nonemptiness holds because \(KD\) itself extends \(g\).

This proves that the complement of the closure of
\(\mathcal N\) contains a nonempty basic subopen
inside every nonempty basic open; hence
\(Z=\overline{\mathcal N}\) is indeed **closed nowhere
dense in the monoid Ellentuck topology**, not merely
nowhere dense in the pointwise topology.

Since every pure \([f,H]\) contains one member of
\(\mathcal N\), no such pure refinement avoids \(Z\).
The dense open complement of \(Z\) also meets each
nonempty pure neighbourhood, so it cannot be Ramsey.

**Disposition:** both conclusions of the original
Theorem 1.11 are refuted at precisely the printed
definitions. Do not confuse this monoid topology
with the independently validated fat-tree topology.

### Referee IV: set theory / cardinal arithmetic

A pairwise almost-disjoint family
\(\{A_\xi:\xi<\mathfrak c\}\), each infinite, is obtained
from branches through the binary tree:
\(A_x=\{\mathrm{code}(x|n):n\ge1\}\).
There are \(\mathfrak c\) such branches and their
pairwise intersections are finite.

The free tree is countable, so the set of all total
self-maps, hence the pure submonoid
\(\mathcal P\), has cardinality at most
\(\aleph_0^{\aleph_0}=\mathfrak c\).
Enumerate all pure \(H_\alpha\) for
\(\alpha<\mathfrak c\) with repetitions if needed.

At stage \(\alpha<\mathfrak c\), each previous
\(K_\beta\) forbids **at most one** choice
\(H_\alpha Q_{A_\xi}\), by Referee II.
The number of previous stages is \(|\alpha|<\mathfrak c\).
The union of fewer than \(\mathfrak c\) singletons
has cardinality below \(\mathfrak c\), **even when
\(\mathfrak c\) is singular**. Choose a free index.
Thus the recursion is valid in ZFC, with no
continuum hypothesis or regularity of \(\mathfrak c\).

### Attempts to invalidate the construction

1. **Remove the root marker:** if every inserted code
   were empty, the compatibility lemma could fail;
   level intersections alone would be insufficient.
   The marker is essential.
2. **Allow \(G(r)=r\):** the no-root-marker lemma
   would fail at a retained image level if source
   parameters include the root. The construction
   deliberately makes every \(K_\alpha(r)=s\).
3. **Use a finite almost-disjoint family:** does not
   force infinitely many mutually incompatible
   candidates after an arbitrary transfinite stage.
4. **Treat two shape maps as compatible if ranges
   intersect:** wrong relation. The proof uses an
   actual common right multiple and the entire
   successor-code history.
5. **Forget that D must fix g:** then the subopen
   \([g,KD]\) can be empty. Choose gap m strictly
   above the last source level of g.
6. **Use Borel coding:** the transfinite Z is only
   shown Ellentuck-closed; it need not be Borel
   in the ordinary pointwise topology. This is why
   there is no contradiction with the separately
   proved pointwise-Borel fat-image result.
7. **Infer the theorem is false merely from
   noncontinuity of the fat projection:** invalid.
   The present argument constructs a *new* set Z
   directly in the **shape-map monoid** and verifies
   failure of the Ramsey-null and Ramsey conclusions.

## Final referee disposition

**English mathematical counterexample: accepted at the
printed M1–M3 and monoid-neighbourhood definitions.**
This is stronger than a gap in Lemma 4.1 and calls for
correcting or qualifying Theorem 1.11 itself.

**Formal validation status:** NOT YET LEAN-CERTIFIED.
The model's M1–M3 theorem is already checked.
The future Lean modules should prove the infinite-mask
shape-map construction, the compatibility marker lemma,
and then the set-theoretic recursion/nowhere-density result.
The existing finite program is useful as a regression, not
a replacement for those proofs.

**Manuscript policy:** leave the author's frozen proof text
unchanged. Add a TODO/referee note only after approval;
preserve both the verified finite shape-Ramsey theorem
and the verified fat-tree Ellentuck theorem.
