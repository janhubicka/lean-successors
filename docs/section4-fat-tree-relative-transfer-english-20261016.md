# Section 4: a fat-tree replacement strategy for shape-map Ellentuck

**Research note, 16 October 2026. English proof and adversarial audit.**
This is not a proposed edit to the frozen manuscript, and none of the
unproved statements below should receive a Lean validation marker.
The original shape-map theorem is Theorem 1.11; the verified fat-tree
Ellentuck theorem is Theorem 1.17.

## 1. What must change

For an \((\mathcal S,\mathcal M)\)-tree write \(\mathcal R\) for its space
of infinite fat trees, \(P(U)=F_U\in\mathcal M\) for the canonical left-product
projection, and \(I\) for the identity fat tree. Recall the actual
neighbourhoods:
\[
 [f,F]_{\mathcal M}=\{F\circ G:G\in\mathcal M,\
       F\circ G\text{ extends }f\},
 \qquad
 [x,U]_{\mathcal R}
   =\{W\le_{\mathrm{fat}}U:W|_{|x|}=x\}.
\]
If \(f=F\circ g\) is a compatible finite prefix (uniqueness follows from
injectivity of \(F\)), let \(d=\operatorname{depth}_F(f)=\widetilde g(n)\),
where \(g\) has source domain \(T^{\le n}\). Thus a pure shape-map
refinement belongs to \([d,F]\) when it agrees with \(F\) on
\(T^{\le d}\). The corresponding *fat-tree approximation length* is
\(m=d+1\).

The verified fat-tree order uses inclusions of lifts, and **does not**
imply \(P(V)=P(U)\circ G\) when \(V\le_{\mathrm{fat}}U\).
This is not an inconsequential indexing error. The one-parameter
free-ancestral witness \(U=(E_0,\mathrm{id},\dots)\),
\(V=(E_0,E_2,\mathrm{id},\dots)\), in which \(E_2\) inserts
parameter \([0]\), has \(V\le_{\mathrm{fat}}U\), but \(P(V)\)
does not factor on the right through \(P(U)=E_0\).
The delayed witnesses \(V_q\) give arbitrarily long identical
finite fat prefixes and show the proposed \(P\) is not
Ellentuck-continuous. See
[the existing adversarial audit](wiki/Fat-Tree-to-Shape-Map-Transfer.md).

**Consequently the printed assertion**
\[
 P([x,U]_{\mathcal R})=[F_x,F_U]_{\mathcal M}
\]
**cannot be used.** The remainder of this note does not ask for
A.3(2) for \(\mathcal M\), since that axiom fails in general.

## 2. Change the direction of the construction: keep \(F\) outside

For every fixed \(F\in\mathcal M\), define
\[
 \rho_F:\mathcal R\longrightarrow\mathcal M,\qquad
 \rho_F(U)=F\circ P(U).
\]
This is not the original map \(P\), except when \(F=\mathrm{id}\).
The point is the *algebraic identity*
\[
 \rho_F(U)\in[\varnothing,F]_{\mathcal M}
 \quad\text{for every fat tree }U.
\]
It requires no compatibility between fat reductions and
right factors. In particular, even if \(V\le_{\mathrm{fat}}U\)
projects badly, \(F\circ P(V)\) is still a right factor of **the
fixed outer map** \(F\).

The existing verified
\`FatTree.projectionRespectsPrefixes\` means that \(P\) is
continuous for **the ordinary finite-approximation/product
topologies**. Composition on the left by a fixed \(F\) is also
pointwise continuous, so \(\rho_F\) is continuous for these
*metric* topologies. This says nothing about its continuity
between the finer Ellentuck topologies.

### Two precise fat-tree lifting statements

We separate the finite and infinite assertions.

**(FR0) Identity-fat finite-stem realization.** If
\(g\in \mathrm{AM}\) has source domain \(T^{\le n}\) and
last image level \(d=\widetilde g(n)\), there is a finite fat
tree \(x\), of height \(n+1\), satisfying
\[
 F_x=g,\qquad
 x\le_{\mathrm{fin}}I|_{d+1},\qquad
 \operatorname{depth}_{I}(x)=d+1.
\]
When \(g\) is empty take \(x\) empty and depth zero. A promising
proof uses the canonical widening of a total extension of \(g\)
(\`ofShapeMap\`) and the fact that the identity fat tree's
iterated lift consists of all descendants on the appropriate level.
The terminal-cut equation is \(x(n+1)=d+1\). The complete finite
\(\le_{\mathrm{fin}}\) proof, including all successor parameters,
still requires checking; the source's Proposition 2.2 and Lean's
\`FatTree.FiniteReduction\` are the intended tools.

**(FR1) Relative right-factor lifting with a fixed stem.**
Let \(x,g,d\) be as in (FR0), and take any
\[
 V\in[d+1,I]_{\mathcal R}
\]
(the entire first \(d+1\) rows of \(V\) are those of the identity
fat tree). For every \(Q\in\mathcal M\) such that
\[
 P(V)\circ Q\text{ extends }g,
\]
there is \(W\in[x,V]_{\mathcal R}\) with
\[
                    P(W)=P(V)\circ Q.                 \tag{FR1}
\]
Equivalently, the **one-sided** inclusion
\[
       [g,P(V)]_{\mathcal M}\subseteq
                    P([x,V]_{\mathcal R})             \tag{1}
\]
holds whenever \(x\) occurs at the required depth of \(V\).
This is the only direction of the old neighbourhood identity
that the following proof uses. It does **not** say that every
geometric reduction of \(V\) projects inside \([g,P(V)]\).

The construction suggested by the manuscript is to factor finite
restrictions of \(P(V)\circ Q\) successively, realize each required
one-row coordinate inside the corresponding fat lift, and splice
the chosen row to the already fixed prefix \(x\). The current Lean
lemmas \`tailCoordinateRow_oneBlockOccurs\`,
\`appendRow_stemAt_of_topRange\` and \`splice_reduces\` verify
important parts of that program. They do **not yet** establish
the exact arbitrary-\(Q\), prescribed-\(x\), all-level assertion
(FR1); that is an explicit remaining proof obligation.

### A sharper route to FR1 (and its remaining obstacle)

The existing Lean identity
\[
 \operatorname{partialMap}(U,i+1)
       =\operatorname{canonicalExtension}(P(U),i)
\]
(\`FatTree.canonicalExtension_associatedMap\`) is useful.
If two finite fat stems represent **the same** finite
shape map through source level i, their canonical partial
products are identical as *total monoid maps*, not merely
on the original source nodes. Thus a **geometrically legal**
replacement of one such stem by the other, with unchanged
boundary cut and unchanged future fat rows, also preserves
the final associated shape map.

One could therefore try to prove FR1 in two stages:

1. For any right factor \(Q\) construct a fat \(W_0\le V\)
   with \(P(W_0)=P(V)\circ Q\), initially without protecting
   x. This is a **right action of M on fat trees** and
   could be built by the checked one-row tail-coordinate
   realization and fusion.
2. If \(P(W_0)\) extends g, prove that the **chosen finite
   stem** x occurs geometrically in \(W_0\) at the appropriate
   terminal cut, then use fat A.3/splicing to place x at the
   beginning. The canonical-extension identity ensures
   that a successful splice does not alter \(P(W_0)\).

The second step is **not automatic**. Equality of a finite
projected map does not imply equality, or even occurrence,
of finite fat stems: each fat row acts on **the entire
target-cut level**, including unused nodes and non-ancestral
successor parameters. A row of x can be incompatible with
the lifts of \(W_0\) on those nodes. A genuinely *universal
finite stem* x, or a proof that all such x are absorbable,
is needed. This is the precise point to test adversarially
before asserting FR1. It is preferable to vague phrases
such as "replace a suitable initial segment".

## 3. A replacement theorem with a complete *conditional* proof

**Conditional fat transfer.** Assume (FR0) and (FR1) for the
\((\mathcal S,\mathcal M)\)-tree, together with the following
relative category properties for all \(F\in\mathcal M\):

- **(RC-open)** If \(O\subseteq\mathcal M\) is open in the
  *shape-map Ellentuck topology*, then
  \(\rho_F^{-1}(O)\) has the property of Baire in the fat-tree
  Ellentuck topology.
- **(RC-null)** If \(N\subseteq\mathcal M\) is meagre in
  the *shape-map Ellentuck topology*, then
  \(\rho_F^{-1}(N)\) is meagre in the fat-tree Ellentuck topology.

Then **every shape-map Ellentuck-Baire set is Ramsey and every
shape-map Ellentuck-meagre set is Ramsey null**, with precisely
the paper's definition of pure refinement. No A.3(2) for
shape maps is needed.

**Proof.** Fix a nonempty \([f,F]_{\mathcal M}\), and write
\(f=F\circ g\). Put \(d=\operatorname{depth}_F(f)\);
obtain \(x\) of fat depth \(m=d+1\) by (FR0).
For the empty prefix take \(m=0\). For a Baire set \(X\),
write \(X=O\mathbin{\triangle}N\), where \(O\) is Ellentuck-open
and \(N\) meagre. By (RC-open) and (RC-null),
\[
        Y_F=\rho_F^{-1}(X)
\]
has the fat-tree Baire property. Apply the *verified* fat-tree
Ellentuck Theorem 1.17 in the nonempty neighbourhood \([x,I]\).
There is
\[
 V\in[m,I]_{\mathcal R}
\]
such that all of \([x,V]_{\mathcal R}\) is in \(Y_F\), or all of
it is disjoint from \(Y_F\).

Set \(F'=F\circ P(V)\).
Because \(V\) preserves the first \(m=d+1\) identity fat rows,
finite-prefix stability gives \(P(V)|_{T^{\le d}}=\mathrm{id}\).
Consequently
\[
                 F'\in[d,F]_{\mathcal M}.             \tag{2}
\]
Now let \(H\in[f,F']_{\mathcal M}\) be arbitrary. We can write
\[
              H=F'\circ Q=F\circ P(V)\circ Q.
\]
Since \(H\) extends \(f=F\circ g\) and \(F\) is injective,
\(P(V)\circ Q\) extends \(g\). By (FR1) there exists
\(W\in[x,V]_{\mathcal R}\) such that \(P(W)=P(V)\circ Q\).
Therefore
\[
                     H=\rho_F(W).
\]
All such \(W\) have the same membership in \(Y_F\), hence
\([f,F']_{\mathcal M}\) is contained in \(X\) or disjoint from
\(X\). **Nonemptiness** is checked independently rather than
inferred from the one-sided inclusion (FR1): choose a total
\(G\in\mathcal M\) extending the finite quotient \(g\).
Because \(P(V)\) fixes all nodes through target level \(d\),
\(P(V)\circ G\) still extends \(g\). Consequently
\(F'\circ G=F\circ P(V)\circ G\) extends \(f\), so
\([f,F']\ne\varnothing\). This proves the Ramsey assertion.

If \(X\) is meagre, (RC-null) says that \(Y_F\) is fat meagre.
Apply the *Ramsey-null* half of fat Ellentuck to obtain the
disjoint alternative. Use exactly (2) and (FR1) again to
conclude \([f,F']\cap X=\varnothing\). QED.

The proof is complete **given the four named ingredients** (FR0, FR1, RC-open, RC-null).
No step invokes \(P([x,V])\subseteq[g,P(V)]\), or any
direct shape-map A.3(2).

## 4. A rigorous weaker target needing no relative category theorem

There is a useful theorem with one fewer gap.

**Conditional pointwise-Borel theorem.** Assuming only
(FR0) and (FR1), *every pointwise-Borel subset of*
\(\mathcal M\) *is Ramsey for the monoid Ellentuck
neighbourhoods*. (Equivalently, a pointwise-Borel finite
colouring of all total shape maps has a homogeneous pure
refinement below every nonempty finite-stem monoid
neighbourhood.)

**Proof.** The already checked finite-prefix lemma implies
that \(\rho_F\) is continuous from the *metric* fat
approximation space to the *metric* space of shape maps.
Hence, if \(X\) is pointwise-Borel, \(Y_F=\rho_F^{-1}(X)\)
is fat metrically Borel. The Ellentuck topology on fat trees
refines the metric topology, so \(Y_F\) is Borel and has the
Baire property in the fat Ellentuck topology. The remainder
is word-for-word the Ramsey half of Section 3, using
(FR0), (FR1) and fat Ellentuck. QED.

This **is not yet an unconditional theorem**, because (FR1)
has not been proved. It is also **strictly less than the
paper's Theorem 1.11**: an arbitrary open set in the monoid
Ellentuck topology need not be pointwise-Borel.

## 4A. An *unconditional* fat-tree replacement (weaker statement)

There is a rigorous theorem that **does not require FR0, FR1,
RC-open or RC-null** and is ready for a separate Lean formulation.

**Theorem (Borel fat-image Ramsey).** Let
\((T,\preceq,\Sigma,\mathcal S,\mathcal M)\) be any
\((\mathcal S,\mathcal M)\)-tree. Let \(X\subseteq\mathcal M\)
be *pointwise-Borel* (in the product topology on total
shape maps). For every nonempty fat-tree neighbourhood
\([x,U]_{\mathcal R}\), there exists
\[
             V\in[\operatorname{depth}_U(x),U]_{\mathcal R}
\]
such that **either**
\[
             P([x,V]_{\mathcal R})\subseteq X
\]
**or**
\[
             P([x,V]_{\mathcal R})\cap X=\varnothing.
\]
Consequently, every pointwise-Borel finite colouring of
\(\mathcal M\) becomes monochromatic on **the entire projected
fat neighbourhood** \(P([x,V])\) after a fat-depth-preserving
refinement.

**Proof.** Set \(Y=P^{-1}(X)\subseteq\mathcal R\).
The verified \`projectionRespectsPrefixes\` states that the
restriction of \(P(W)\) through source level \(n-1\) depends
only on the first \(n\) fat rows of \(W\). Therefore \(P\)
is continuous from the metric fat approximation topology
into the pointwise topology on \(\mathcal M\).
It follows that \(Y\) is Borel for the metric topology
on \(\mathcal R\). Since the fat Ellentuck topology refines
its metric topology, \(Y\) is also Ellentuck-Borel and
in particular has the fat Ellentuck Baire property.

Apply the **verified fat-tree Theorem 1.17** to \(Y\)
in \([x,U]\). It gives a pure fat refinement \(V\) such that
the whole of \([x,V]\) lies in or outside \(Y\).
Taking images under \(P\) gives the two displayed
alternatives. For finitely many Borel colours, apply the
two-colour version consecutively, using transitivity
of fat refinement and retaining the same protected
stem; nonemptiness of each protected neighbourhood
comes from the proved fat A.3(1). QED.

**Referee boundary:** this is a genuine infinite-dimensional
Borel Ramsey statement **about projections of fat-tree
neighbourhoods**, *not* the printed Theorem 1.11.
Its homogeneous set is \(P([x,V])\), which may contain
shape maps outside the algebraic monoid cone \([F_x,F_V]\).
No implication that a monoid neighbourhood \([f,F']\)
is homogeneous follows. This distinction is forced by
the free-ancestral counterexample. The theorem is
nevertheless useful independently of the truth of 1.11,
and its English proof has no missing lifting or
category-transfer assumption.

## 5. Adversarial audit: two major gaps

### Referee A — geometric relative lifting

(FR1) must be proved for **every** monoid right factor \(Q\)
and for the **specified** finite fat stem \(x\). It is
not enough to show that the range of \(P(V)\circ Q\) lies
in the geometric subtree \(T_V\); that is only the paper's
\(F\le^\circ V\), not an algebraic lifting construction.

A proof must maintain, at every new source level \(i\):

1. The chosen finite fat tree is a *genuine finite reduction*
   of \(V\), with a strictly increasing selected-cut index and
   correct oneLift inclusion on the **whole starting level**,
   not merely on the protected image of a source map.
2. Its associated partial map equals
   \((P(V)\circ Q)|_{T^{\le i}}\).
3. Its first \(|x|\) rows remain **literally** \(x\); a replacement
   of an arbitrarily produced prefix by \(x\) is not
   automatically legal, especially at the splice junction.
4. The finite witnesses form coherent initial segments and
   have an unbounded sequence of cuts. Their fusion is a
   fat tree reducing \(V\), not just a limit of partial
   shape maps.

The available \`tailCoordinateRow_oneBlockOccurs\`
supplies a one-row occurrence, but it does not on its own
extend an arbitrarily prescribed earlier fat prefix.
The published text's final instruction "replace a suitable
initial segment by \(x\)" is precisely where this needs checking.

**Disposition A:** plausible programme from M2 and the
fat-tree splice library; no complete proof yet.

### Referee B — Baire/category preservation

The original projection \(P\) is not continuous for the
Ellentuck topologies; the free-ancestral \(V_q\) witnesses
prove the failure at the level of the *claimed proof*.
Consequently there is no justification for asserting that
\(\rho_F^{-1}(O)\) is open whenever \(O\) is a monoid
Ellentuck-open set.

Being **metrically continuous** only gives the
pointwise-Borel theorem of Section 4. It does not
give (RC-open) for arbitrary uncountable unions of monoid
basic neighbourhoods, nor (RC-null) for meagre sets in
the *finer* monoid topology.

A possible route would be a separate **fat pure-decision
lemma**: using genuinely finite row/stem data, show that
the preimage of every monoid-open set is Baire in the
fat-tree space and the preimage of each monoid nowhere
dense set is fat meagre. To avoid circularity, this must
be proved directly by **fat-tree A.4, stem amalgamation
and fusion**. Merely applying fat Ellentuck to the
pullback is circular until the pullback is known to
be Baire.

**Disposition B:** this is a substantive new infinite
dimensional result and might be false. It is the chief
obstacle to an unconditional proof of Theorem 1.11.

### Referee C — can Theorem 1.11 itself fail?

Failure of the specific projection in Lemma 4.1 is **not**
a counterexample to Theorem 1.11. But a distinct
counterexample must be ruled out before investing in
a difficult category-preservation proof.

An earlier research attempt proposed a closed nowhere-dense
but non-Ramsey-null set \(Z\), using nearly disjoint
infinite level sets and shape maps with a marked root
parameter. It has not been independently reconstructed
or checked in the current Lean codebase. In particular,
one must prove separately:

- \(Z\) is really nowhere dense in the **monoid Ellentuck**
  topology (not merely in the product topology);
- it meets \([f,H]\) for **every** pure \(H\in[d,F]\);
- every \(Q_A\) used in its definition is genuinely in the
  chosen (S,M)-tree monoid, with the stated successor
  parameters and no illicit partial functions.

If all three hold, Theorem 1.11 as printed is false, and
there cannot be a full replacement proof from M1–M3.
Until then it is only a **counterexample candidate**,
not a refutation. The successful finite \(\pi\) counterexample
does **not** establish these stronger properties.

**Disposition C:** mandatory adversarial check before any
unqualified "Theorem 1.11 verified" statement.

## 6. Recommended mathematics-first sequence

1. **Finish FR0.** Establish finite factor-stem realization
   inside the identity fat tree, with the exact \(d+1\) cut.
   This should be short using the existing canonical widening.
2. **Attack FR1**, *not A.3(2) for the monoid*. Prove a relative
   finite one-block lifting lemma with a literal prescribed
   fat stem. Iterate using the verified
   \`tailCoordinateRow_oneBlockOccurs\` and
   \`splice_reduces\`; audit the junction and limit.
3. Once FR1 survives an adversarial review, the **pointwise-Borel
   Ramsey theorem** follows immediately from Section 4.
   This is a useful standalone theorem to state and eventually
   validate, regardless of the ultimate status of 1.11.
4. In parallel, independently audit the potential nowhere
   dense non-Ramsey-null set \(Z\). Its success would decide
   the status of the *full* theorem.
5. If the candidate \(Z\) fails, attempt the fat
   category/pure-decision lemma (RC-open, RC-null).
   For reference, weaker-than-A.3(2) amalgamation
   frameworks exist (Dobrinen--Zucker, arXiv:2303.04246),
   but this project should **continue to use fat trees**
   rather than assert direct shape-map A.3(2).

### Exact current status

- **Verified in Lean:** the fat-tree Theorem 1.17, its A.3(2)
  and A.4; the finite shape Ramsey Theorem 1.6; projection
  surjectivity and finite-prefix stability.
- **Counterexample in progress:** algebraic free-ancestral
  nonfactorization and arbitrarily delayed geometric
  witnesses; the full infinite latter still needs kernel
  verification.
- **English proof completed unconditionally:** Section 4A,
  pointwise-Borel Ramsey homogeneity on projected **fat**
  neighbourhoods; this is a strictly weaker, sound theorem.
- **English proof completed conditionally:** Section 3 of
  this note, with FR0, FR1, RC-open, RC-null explicit.
- **English pointwise-Borel transfer completed conditionally:**
  Section 4, requiring FR0 and FR1 only.
- **Not proved:** FR1, the category regularity statements,
  or the full Theorem 1.11. Do not issue a green validation
  marker for them yet.

The frozen manuscript proof is untouched. This note is an
independent proposal for author/referee review prior to Lean
implementation.
