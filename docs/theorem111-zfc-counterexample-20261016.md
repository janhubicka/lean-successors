# A ZFC counterexample to the shape-map Ellentuck theorem (Theorem 1.11)

**16 October 2026 — new English proof for adversarial review.**

The following gives a counterexample to **the statement** of
Theorem 1.11 in the successor-tree manuscript, not merely to the
projection Lemma 4.1. The example is the verified free-ancestral
successor tree with one letter and one ancestral parameter, equipped
with its **full shape-preserving monoid**. Its construction relies on
the axiom of choice (via a continuum-length recursion), but does
**not** require CH or any additional set-theoretic hypothesis.

**Theorem.** There are an \((\mathcal S,\mathcal M)\)-tree satisfying
the original M1–M3 axioms, a finite shape map \(f\), and a set
\(Z\subseteq\mathcal M\) such that

1. \(Z\) is closed nowhere dense in the **monoid Ellentuck topology**
   of Definition 1.9;
2. the basic neighborhood \([f,\mathrm{Id}]\) is nonempty; and
3. for **every** pure refinement
   \(H\in[\operatorname{depth}_{\mathrm{Id}}(f),\mathrm{Id}]\),
   \[
                         [f,H]\cap Z\ne\varnothing .
   \]

Thus \(Z\) is meagre but not Ramsey null. In fact
\(\mathcal M\setminus Z\) is a **dense open set which is not Ramsey**.
Both assertions of Theorem 1.11 fail as currently stated.

## 1. The genuine free-ancestral (S,M)-tree

Let the alphabet consist of one letter, and allow at most one
ancestral parameter. A node of source level \(n\) is a history
\[
 h=(c_0,\ldots,c_{n-1}),\qquad
 c_i\in\{\varnothing\}\cup\{(k):0\le k<i\}.
\]
The partial successor operation appends a code \(c_n\); a parameter
\((k)\) denotes the unique ancestor of \(h\) at level \(k\).
The order is history extension. Write \(r=()\) for the root,
and \(s=(\varnothing)\) for the unique level-one node.

Let \(\mathcal M\) consist of **all** shape-preserving self maps of
this tree. This is the Lean-verified instance
\`FreeAncestral.freeSMTree (Label := Unit) (arity := 1)\`:
M1 (closure/fusion), M2 (splitting skipped levels), and M3
(duplication of a level) have actual proofs. In particular,
each \(F\in\mathcal M\) has a strictly increasing image-level
map \(\lambda_F:\omega\to\omega\). Set
\[
 f:T^{\le0}\to T,\quad f(r)=s,\qquad
 \mathcal P=[1,\mathrm{Id}]
 =\{H\in\mathcal M:H|_{T^{\le1}}=\mathrm{Id}\}.
\]
Since \(f\) extends to shape maps below, \(f\in\mathrm{AM}\) and
\(\operatorname{depth}_{\mathrm{Id}}(f)=1\). All maps
\(H\in\mathcal P\) fix both \(r\) and \(s\).

Two maps \(G,K\in\mathcal M\) are **compatible**, written
\(G\parallel K\), if there exist \(R,S\in\mathcal M\) with
\[
                       G\circ R=K\circ S.
\]
Thus they have a common *algebraic right multiple* (a common
right-composition refinement). This is **not** geometric
fat-tree reduction.

## 2. Explicitly marked maps Q_A

Fix an infinite set \(A\subseteq\{2,3,\ldots\}\).
Enumerate \(L_A=\{1\}\cup A\) increasingly:
\[
            1=\ell_0<\ell_1<\ell_2<\cdots.
\]
Define \(Q_A\) recursively on all finite histories.

First, \(Q_A(r)=s=(\varnothing)\). If \(h\) is a
source node of level \(n\) and \(h^\frown c\) is a
successor, put
\[
 Q_A(h^\frown c)
   =Q_A(h)^\frown \widehat c\,^\frown
       \underbrace{(0)^\frown\cdots^\frown(0)}
                    _{\ell_{n+1}-\ell_n-1\ {\rm copies}},
 \tag{2.1}
\]
where \(\widehat c=\varnothing\) if \(c=\varnothing\),
and \(\widehat c=(\ell_k)\) if \(c=(k)\).
The appended symbol \((0)\) is the **parameter pointing
to the original root \(r\)**, not the unique letter of
the alphabet.

Formula (2.1) has three key properties.

**(P1) Genuine shape map.**
At the first new target step after \(\ell_n\), (2.1)
reproduces exactly the image of the original successor
parameters, so the required weak successor is a prefix
of \(Q_A(h^\frown c)\). All additional \((0)\)-steps
are legitimate ancestral successors, since the root
lies below every node. Distinct child codes \(c\)
have distinct immediate successor images
(\(\ell_k\) is injective), hence remain separated
under their later extensions. Distinct source levels
map to the strictly increasing levels \(\ell_n\);
the root image \(s\) lies above \(r\). Consequently
\[
             Q_A\in\mathcal M,\qquad
             \lambda_{Q_A}(n)=\ell_n,\qquad Q_A(r)=s.
 \tag{2.2}
\]
These assertions can also be proved by straightforward
induction on source history length.

**(P2) A root marker after every omitted level.**
For every target level \(j\ge2\) with \(j\notin A\),
the edge from level \(j\) to \(j+1\) on the ancestor
path to **any sufficiently high** \(Q_A(h)\) has
parameter \(r\) (code \((0)\)). Indeed, \(j\) lies
strictly between successive \(\ell_n,\ell_{n+1}\),
so the relevant output step in (2.1) is one of the
added root-marker steps.

**(P3) No root marker immediately after a retained
image level.** For \(t=\ell_n\), the edge at target
level \(t+1\) on a sufficiently high \(Q_A(h)\)
is the obligatory first successor step \(\widehat c\)
from (2.1). Its parameter list is empty or refers
to a target ancestor at some level \(\ell_k\ge1\);
hence it is **never** the root parameter \((0)\).

The crucial distinction is **j omitted versus j retained**,
and the code on the edge **from j to j+1**, rather
than the code ending *at j*. Confusing these two
coordinates invalidates the argument.

## 3. A universal "no root marker" observation

**Lemma 3.1.** Let \(G\in\mathcal M\) satisfy \(G(r)=s\).
For every retained target level \(t=\lambda_G(k)\),
the edge from target level \(t\) to \(t+1\)
on the ancestor path to **every sufficiently high**
\(G(h)\) does **not** use parameter \(r\).

**Proof.** Let \(h\) have source level \(>k\);
let \(a=h|_k\) and \(b=h|_{k+1}\). Write
\(b=\mathcal S(a,p,c)\), where the unique
parameter, if present, is a source ancestor below
level \(k\). By shape preservation,
\(\mathcal S(G(a),G(p),c)\preceq G(b)\preceq G(h)\).
This is the **immediate** outgoing edge after \(G(a)\)
at target level \(\lambda_G(k)=t\).
If \(p\) is present, its image lies on a target
level at least \(\lambda_G(0)=1\), so \(G(p)\ne r\).
If no parameter is present, the code is empty.
Either way the edge at \(t+1\) is not marked
by \(r\). \(\square\)

**Lemma 3.2 (transport of the root marker).**
Suppose \(H\in\mathcal P\). If \(j\notin A\)
and \(j\ge2\), then on every sufficiently high
\(H(Q_A(h))\) the edge from target level
\(\lambda_H(j)\) to \(\lambda_H(j)+1\)
has parameter \(r\).

**Proof.** By (P2), on a sufficiently high \(Q_A(h)\)
the edge from source level \(j\) to \(j+1\)
uses the root parameter \(r\). By the weak
successor-preservation clause of the shape-map
definition, applying \(H\) sends this edge
to a path whose **first** edge above \(H(a)\)
has parameter \(H(r)\). Pure \(H\) fixes \(r\),
so this parameter is again \(r\). Since
\(\operatorname{lev}(H(a))=\lambda_H(j)\),
the asserted target edge is obtained. \(\square\)

## 4. The decisive compatibility lemma

For \(G(r)=s\) and \(H\in\mathcal P\), set
\[
 D_G^H=\{j\ge2:\lambda_H(j)\in\lambda_G[\omega]\}.
 \tag{4.1}
\]

**Lemma 4.1 (compatibility forces an almost-disjoint
support inclusion).** If
\[
                    G\parallel (H\circ Q_A),
\]
then \(D_G^H\) is infinite and
\[
                              D_G^H\subseteq A.
 \tag{4.2}
\]

**Proof.** Choose total shape maps \(R,S\) such that
\[
                C=G\circ R=H\circ Q_A\circ S.
\]
The image-level set \(\lambda_C[\omega]\) is
infinite, and lies in
\(\lambda_G[\omega]\cap\lambda_H[\omega]\).
Because \(\lambda_H\) is injective, (4.1)
is therefore infinite.

Suppose \(j\in D_G^H\setminus A\), and write
\[
                  t=\lambda_H(j)=\lambda_G(k).
\]
Choose a source node \(h\) of C at a sufficiently
high level that the common value \(C(h)\) lies
above \(t+1\), and that the input nodes \(R(h)\)
and \(S(h)\) pass the finitely many levels involved.
This is possible because every shape map has
strictly increasing, unbounded level map.

Since \(t\) is **retained** by \(G\), Lemma 3.1
says that the edge at target level \(t+1\)
of \(G(R(h))=C(h)\) does **not** use root
parameter \(r\).

Since \(j\notin A\), Lemma 3.2 says that
the same edge at target level \(t+1\) of
\(H(Q_A(S(h)))=C(h)\) **does** use \(r\).
A finite history cannot have both successor
codes on the same edge. Contradiction.
Hence no such \(j\) exists, proving (4.2).
\(\square\)

**Corollary 4.2.** Let \(\{A_\xi:\xi<\mathfrak c\}\)
be any pairwise almost-disjoint family of infinite
subsets of \(\{2,3,\ldots\}\), where
\(\mathfrak c=2^{\aleph_0}\). For fixed
\(G(r)=s\) and fixed pure \(H\),
there is **at most one** \(\xi<\mathfrak c\)
for which \(G\parallel H\circ Q_{A_\xi}\).

Indeed, otherwise the infinite set \(D_G^H\)
would be contained in two almost-disjoint
sets, contradicting finite intersection.

This is much stronger than merely saying
\(\lambda_G[\omega]\cap\lambda_{HQ_A}[\omega]\)
is infinite. The *successor parameter at
the first edge after a retained level*
is precisely what forces **containment**
\(D_G^H\subseteq A\), rather than merely
an infinite intersection. This is also
the step requiring the most careful
adversarial checking.

## 5. A nowhere-dense transversal to every pure cone (in ZFC)

Choose a pairwise almost-disjoint family
\(\{A_\xi:\xi<\mathfrak c\}\) as above.
For example, fix an injection
\(\mathrm{code}:2^{<\omega}\to\{2,3,\ldots\}\)
and for \(x\in2^\omega\) put
\[
 A_x=\{\mathrm{code}(x|_n):n\ge1\}.
\]
Distinct infinite binary sequences share
only finitely many initial segments, so
their sets \(A_x\) have finite intersection.

Since the free tree \(T\) is countable,
\(|\mathcal P|\le\mathfrak c\).
Enumerate **all** pure refinements,
with repetitions if necessary, as
\[
                  (H_\alpha)_{\alpha<\mathfrak c}.
\]

Construct by transfinite recursion a family
\[
                 \mathcal N=\{K_\alpha:
                                      \alpha<\mathfrak c\}
\]
with \(K_\alpha(r)=s\) and

- \(K_\alpha\in[f,H_\alpha]\);
- \(K_\alpha\) and \(K_\beta\) have **no common
  algebraic right multiple** whenever \(\beta<\alpha\).

At stage \(\alpha\), consider candidates
\(H_\alpha\circ Q_{A_\xi}\), all lying
in \([f,H_\alpha]\). For each previously
chosen \(K_\beta\), Corollary 4.2 says
that **at most one** index \(\xi\) is
forbidden by compatibility with \(K_\beta\).
There are \(|\alpha|<\mathfrak c\)
previous choices. Hence fewer than
\(\mathfrak c\) indices are forbidden;
choose a remaining \(\xi\) and set
\[
                 K_\alpha=H_\alpha\circ Q_{A_\xi}.
\]
This works without any regularity
assumption on \(\mathfrak c\): for each
\(\alpha<\mathfrak c\), the union of
\(|\alpha|\) singletons has size
\(<\mathfrak c\).

The resulting \(\mathcal N\) is pairwise
incompatible and meets **every** pure cone
\([f,H]\) with \(H\in[1,\mathrm{Id}]\).

**Lemma 5.1.** Every pairwise incompatible
family of total shape maps is nowhere
dense in the monoid Ellentuck topology,
provided arbitrarily deep nontrivial
one-gap right refinements are available.
In particular, \(\mathcal N\) is nowhere dense.

**Proof.** Let \([g,F]\) be any nonempty
monoid basic neighbourhood. If it misses
\(\mathcal N\), it is already a nonempty
open subset disjoint from \(\mathcal N\).
Otherwise choose
\[
                         K\in[g,F]\cap\mathcal N.
\]
Let the domain of \(g\) be \(T^{\le n}\).
Choose a nontrivial one-gap shape map
\(D\in\mathcal M\) fixing
\(T^{\le n}\), with a **proper** image-level
range (choose its skipped level above n).
Such \(D\) exists explicitly in the free
tree and also follows from the M3
duplication machinery. Put \(K'=K\circ D\).
Then \(K'\) extends \(g\) and
\[
              \varnothing\ne[g,K']\subseteq[g,F].
\]
If some \(J\in\mathcal N\) belonged to
\([g,K']\), then \(J\) would be a common
right multiple of \(J\) and \(K\);
pairwise incompatibility forces \(J=K\).
But \(K\) cannot factor through \(K'\):
an identity
\(K=K\circ D\circ R\) would, by
injectivity of \(K\), give
\(\mathrm{Id}=D\circ R\),
contradicting the skipped target level
in the range of \(D\). Hence
\([g,K']\cap\mathcal N=\varnothing\).

Every nonempty basic open set thus
contains a nonempty basic open subset
disjoint from \(\mathcal N\).
Therefore \(\mathcal N\) is nowhere dense.
\(\square\)

**Finish.** Take
\[
                       Z=\overline{\mathcal N}
\]
in the **monoid Ellentuck topology**.
By Lemma 5.1, \(Z\) is closed nowhere dense,
hence meagre. For every pure
\(H\in[1,\mathrm{Id}]\), the construction
supplies \(K_\alpha\in[f,H]\cap\mathcal N\),
so
\[
                       Z\cap[f,H]\ne\varnothing.
\]
Thus **no** pure refinement of \([f,\mathrm{Id}]\)
avoids \(Z\): \(Z\) is not Ramsey null,
contradicting Theorem 1.11.

Moreover \(O=\mathcal M\setminus Z\) is
**dense open**. Every nonempty pure
\([f,H]\) meets \(Z\) by construction
and meets \(O\) because \(Z\) is nowhere
dense and \([f,H]\) is a nonempty open
set. Therefore **no** pure
\([f,H]\) is homogeneous for \(O\):
\(O\) is not Ramsey. This refutes the
Baire-set half of Theorem 1.11 as well.
\(\qquad\square\)

## 6. Why this does not contradict the checked theorems

- The theorem concerns an **uncountably constructed
  Ellentuck-closed set**, not a pointwise-Borel set.
  Its definition is not asserted to be Borel for
  the ordinary pointwise topology.
- The **fat-tree Ellentuck Theorem 1.17** remains
  unaffected. Its fat reductions genuinely satisfy
  A.3(2), and its geometric topology is different.
- The **finite-dimensional shape-Ramsey
  Theorem 1.6** also remains valid; nothing
  here produces a bad finite colouring of
  one-step shape maps.
- The failure of the projected-neighbourhood
  identity in the printed Lemma 4.1 is a
  separate, *simpler* obstruction. The set
  \(Z\) constructed here refutes the **conclusion**
  of Theorem 1.11, not merely its published proof.

A natural correction is to remove or appropriately
qualify Theorem 1.11, retaining the checked
fat-tree theorem. The previously written
English proof of the **pointwise-Borel fat-image
Ramsey theorem** remains valid; it does not
imply the false monoid Ellentuck-Baire
statement. Before proposing an alternative
positive shape-map theorem, one should
determine precisely which weaker Borel
or restricted-monoid conclusions survive.

## 7. Current verification status

This is a **complete English ZFC counterexample**,
subject to independent mathematical review.
The finite history-code mask identities have been
checked computationally through source level 5
for several masks and pure one-gap maps.
The construction of \(Q_A\), Lemmas 3.1–4.1,
and the transfinite nowhere-dense argument have
**not yet been formalized as Lean theorems**.

This note does not modify the frozen author's
manuscript. Only TODO/referee commentary should
be copied into the manuscript until the authors
review the proposed counterexample.
