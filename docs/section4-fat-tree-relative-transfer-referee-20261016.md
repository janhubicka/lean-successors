# Adversarial referee audit of the proposed Section 4 replacement

**16 October 2026. Mathematics-first review; no Lean formalization
of the replacement requested at this stage.**

Companion proposal:
[English replacement proof](section4-fat-tree-relative-transfer-english-20261016.md).
Manuscript Theorem 1.11 concerns **all subsets of the shape-map monoid
having the Baire property in its Ellentuck topology**; it is stronger
than the existing verified Theorem 1.6 (finite shape Ramsey) and
Theorem 1.17 (fat-tree Ellentuck).

This is a three-angle adversarial *self-audit*, not a claim that
three external mathematicians independently endorsed the result.

## Referee 1: formal statement and quantifiers

**Observation R1.** The replacement does not need the false
geometric-to-algebraic forward implication
\(P(W)\in[\varnothing,P(V)]\) for \(W\le_{\rm fat}V\).
Using \(\rho_F(W)=F\circ P(W)\) makes every candidate a genuine
right factor of the **fixed outer** F. This is the essential
difference from the printed Lemma 4.1.

**Observation R2.** One cannot take an arbitrary fat
refinement W and use \(F\circ P(W)\) as the **pure** refinement
in Definition 1.10: only fat trees V preserving the first
\(m=d+1\) rows of the identity fat tree ensure
\(F\circ P(V)\in[d,F]\). The finite prefix lemma verifies
\(P(V)|_{\le d}=\mathrm{id}\). The \(+1\) is obligatory.

**Observation R3: corrected logical flaw.** One-sided lifting
\([g,P(V)]\subseteq P([x,V])\) does **not** by itself prove that
the refined monoid cone \([f,F\circ P(V)]\) is nonempty.
The replacement proof was corrected: take an actual total
extension G of g; since P(V) fixes all values of G on the
finite source initial segment, \(F\circ P(V)\circ G\)
is an element of \([f,F\circ P(V)]\). Do not instead infer
nonemptiness directly from fat A.3(1).

**Observation R4.** The empty f case has depth \(-1\) in
the paper, and corresponds to the empty fat stem and
approximation length 0, not a fictitious negative Lean index.

**Disposition 1:** the *conditional* proof is logically
sound after the explicit nonemptiness correction. There is
no unconditional theorem yet.

## Referee 2: geometry and finite-row realization

**Danger G1: relative lifting.** The Lean theorem
\`tailCoordinateRow_oneBlockOccurs\` is a statement about
one row of a prescribed **tail map**. It is not the
unqualified extension theorem
\[
 P(V)\circ Q\ \text{extends }g
 \quad\Longrightarrow\quad
 \exists W\in[x,V]\ P(W)=P(V)\circ Q .
\]
Proving the implication requires an induction invariant
that keeps the first \(|x|\) rows *literally* unchanged
while refining the **whole target cut level**, including
nodes not used by the visible source map.

**Danger G2: prescribed stem.** The manuscript's instruction
to replace an already built fat refinement's initial
segment by x can destroy its oneLift inclusions at the
junction and can change the total projected map.
The pre-existing verified \`splice_reduces\` works only
under its exact finite-reduction/terminal-cut hypotheses,
which must be supplied afresh.

**Danger G3: fusion.** A chain of finite fat reductions
does not automatically yield a common infinite fat
reduction. The selected-cut maps must be coherent and
strictly increasing, and the infinite tail rows must
respect the reduction witness. M1 fusion of shape maps
alone is insufficient.

**Danger G3b: non-ancestral parameter dependencies.** The concrete
free-ancestral example is *not* by itself a sufficient test of FR1
for general S-trees. In that example all parameters are ancestors
on the same history spine, so unused branches can often be
completed independently. The abstract axioms S1--S3 allow
parameters to be nodes on *other* branches below the base
level. A row extension prescribed on the visible source image
may then force values on unused cut-level nodes which conflict
with a previously fixed row of x. The global extension of those
side-branch parameters is an indispensable check, not an
artifact of Lean's dependent types.

**Danger G4: identity reservoir.** The finite fat tree
x realizing quotient g must occur *at ambient identity
cut d+1*; it is not enough that x merely projects to g
in some unrelated fat tree.

**Disposition 2:** FR0 is likely accessible with
\`ofShapeMap\`, identity fat rows, M2 and the finite
reduction lemmas. FR1 is plausible but still contains
a nontrivial **global unused-node / non-ancestral parameter** obstruction.
Do not promote the one-row theorem to FR1 without
the explicit induction and splice proof.

## Referee 3: category and scope of the conclusion

**Fatal gap C1.** The map \(P:\mathcal R\to\mathcal M\)
is continuous in the *metric/finite-approximation
topologies* but discontinuous in the shape-map
Ellentuck topology. Hence the replacement **cannot**
say "preimages of monoid-open sets are fat-open".
This is exactly where the printed proof fails.

**Gap C2.** For pointwise-Borel colourings, no new
category claim is required. Metric continuity means
\(\rho_F^{-1}(X)\) is fat metrically Borel, hence
fat Ellentuck-Borel and fat Baire. Conditional on
FR0/FR1, this yields a genuine replacement proof for
all pointwise-Borel X.

**Fatal gap C3.** For full Theorem 1.11, the two
properties RC-open and RC-null are separately needed.
In particular,
\[
  N \text{ monoid-Ellentuck nowhere dense}
  \not\Rightarrow \rho_F^{-1}(N)\text{ fat meagre}
\]
by elementary topology: \(\rho_F\) is not a continuous
open map for the relevant finer topologies. The statement
*may* be true by a nontrivial fat-tree fusion theorem,
but this is currently only a conjecture.

**Gap C4.** It does not suffice to verify the fat Baire
property for preimages of **each individual monoid
basic neighbourhood**. An arbitrary Ellentuck-open
set is an unrestricted (possibly uncountable) union
of such neighbourhoods, while the Baire-property
sets form only a \(\sigma\)-algebra.
A new *uniform open-set decision* lemma is required.

**Gap C5.** Fat-tree Ellentuck cannot be applied
directly to \(Y_F=\rho_F^{-1}(X)\) in order to prove
its own Baire regularity. That would be a circular
proof. The category properties must be established
from the finite successor/fat fusion machinery first.

**Disposition 3:** FR0+FR1 could yield an important
pointwise-Borel theorem. FR0+FR1+RC-open+RC-null
does yield the **full** theorem, but the category
assertions are a major, currently unresolved problem.

## Positive result that survives every objection

The companion note's **Section 4A** gives an **unconditional**
Borel fat-image Ramsey theorem:
\[
  X\subseteq\mathcal M\text{ pointwise-Borel}
  \Longrightarrow
  \forall[x,U]\ne\varnothing\ \exists
     V\in[\operatorname{depth}_U(x),U]
  \quad P([x,V])\subseteq X
     \ \text{or}\ P([x,V])\cap X=\varnothing.
\]
This uses only the checked fat-tree Ellentuck theorem and
the checked *metric* finite-prefix continuity of \(P\).
Both are independent of the disproved monoid-Ellentuck
continuity claim. The proof needs **neither FR1 nor
RC-open/RC-null**, so is a valid immediate target for
Lean statement validation.

**Extra audit of this unconditional theorem:**

- Metric-open finite-prefix cylinders in the fat space
  are Ellentuck-open, since each point has a fat basic
  neighbourhood preserving its finite prefix. Thus
  "pointwise-Borel pullback is fat Ellentuck-Baire" is valid.
- Sequential finite-colour stabilization retains the fat
  stem and depth using fat A.3(2) and transitivity;
  each resulting fat neighbourhood is nonempty by A.3(1).
- The conclusion is *not* that
  \([F_x,P(V)]_{\mathcal M}\) is monochromatic.
  The geometric image \(P([x,V])\) can contain maps
  which do not factor through \(P(V)\). Confusing
  these outputs would reintroduce the false Lemma 4.1.

**Disposition:** English proof accepted at its **weaker,
fat-image** statement. Formalize this before investing in
the more speculative full Theorem 1.11 transfer.

## Additional adversarial alternatives

**Alternative A: reverse composition of fat rows.**
Changing the projection from the left-ordered product
\(u_{i}^{+}\circ\cdots\circ u_0^{+}\)
to the right-ordered product
\(u_0^{+}\circ\cdots\circ u_i^{+}\)
would rescue the simple \(E_0,E_2\) factorization
*in that example*, but breaks the canonical finite
cut formula and generally loses surjectivity. Indeed,
any such right product beginning with E0 must lie in
the algebraic right cone E0M, whereas E2E0 shares
E0's initial root image but provably lies outside E0M.
So this does **not** repair the original theorem.

**Alternative B: redefine fat reduction to force
\(P(W)\le P(V)\).** Then one has changed the fat
space, its basic neighbourhoods, and potentially
A.3(2) and A.4. The already kernel-verified
\`fatTreeEllentuck\` does not transfer automatically
to the new order. It is not a short proof patch.

**Alternative C: a cofinal "parameter-saturated"
subspace of fat trees.** One could hope for a
special family of fat reservoirs on which right-factor
lifting and category regularity are stable. Such
a family must be proved sufficiently dense and must
retain a genuine fat Ramsey/fusion theorem. The
free-ancestral delayed-insertion example rules out
the naive condition "every geometric refinement
projects to a factor" on the entire fat space.

**Alternative D: the theorem itself may need a
qualification.** An earlier possible counterexample
was proposed using a closed nowhere-dense set Z of
shape maps indexed by almost-disjoint sets of levels.
Before treating that as a refutation, its three
assertions must be reconstructed and checked:
(1) Z is Ellentuck nowhere dense;
(2) every pure refinement of one fixed [f,F]
meets Z; (3) all chosen maps are genuinely in
the (S,M)-monoid. The argument is **not validated**.
The failure of the original projection alone does
not refute Theorem 1.11.

## Concrete proof tasks and stop conditions

| Order | Precise task | Sufficient evidence |
| --- | --- | --- |
| 1 | Prove FR0, with terminal cut d+1 | Detailed finite \`LeFin\` proof, no "obvious inclusion" |
| 2 | Prove/disprove FR1 for identity ambient and fixed x | Inductive finite-row construction covering *all* nodes; exact splice and fusion |
| 3 | Obtain Borel monoid-neighbourhood conclusion | Apply conditional proof after tasks 1–2; **separate** from already proved Borel fat-image theorem |
| 4 | Independently check the nowhere-dense Z candidate | Closedness, meagreness and all-pure unavoidability proved, or explicit flaw |
| 5 | Prove/disprove RC-open and RC-null by *fat* decision/fusion | No appeal to shape-map A.3(2), no circular pullback argument |
| 6 | Only then validate full Theorem 1.11 | Complete unconditional English proof, adversarially reviewed, with hypotheses exactly as printed |

**Stop condition:** if either FR1 or RC-null has a
counterexample in a bona fide (S,M)-tree, do not
reinterpret the old Lemma 4.1 as a proof. Work on
a corrected statement or a genuinely different
construction instead.

## Conclusion

The "fixed outer factor + fat-tree homogeneity" idea
**repairs the algebraic direction** that invalidated
the printed projection argument, and gives a clean
conditional Borel Ramsey theorem.

It **does not yet repair the Baire/category argument**
for Theorem 1.11, and the fixed-stem relative lifting
lemma remains a substantial proof obligation.

The appropriate next step is **English verification of FR1**,
with the free-ancestral example serving as an adversarial
test; in parallel test the prior closed nowhere-dense
counterexample claim before attempting RC-null.
No Lean implementation of these conjectural steps
should be considered a finished manuscript validation.
