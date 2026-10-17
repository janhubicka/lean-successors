# Independent adversarial audit of relative EA2

Date: 17 October 2026.

## Scope and verdict

The audit began from the actual diffs of PRs [572](https://github.com/janhubicka/lean-successors/pull/572), [573](https://github.com/janhubicka/lean-successors/pull/573), [575](https://github.com/janhubicka/lean-successors/pull/575), and [576](https://github.com/janhubicka/lean-successors/pull/576), and then read the corresponding files at commit `c256eb9b66410ca1499ccfae0804690e65eb7823`. It also checked Section 4 of the reconstructed manuscript, originally lines 893–1084 of `main.tex`, and the proposed October 17 source patch. No concrete monoid instance or big Ramsey degree application was assumed.

**The mathematical category bridge and conditional transfer are correct.** They use a common fat-tree witness, preserve the source stem, apply A3(2) only to fat trees, and obtain the entire target cone from an explicit covering hypothesis. They do not infer monoid Ellentuck continuity from pointwise continuity.

There are useful exact simplifications. The category test may be restricted to **closed** nowhere dense target sets. On a fixed witness, the two resulting tests are equivalent to preserving both Baire sets and meager sets under inverse image. On the actual fat Ellentuck witness there is a further exact formulation: **EA2 is equivalent to Baire inverse images of all open target sets, together with somewhere dense images of every nonempty relatively open subset of the witness. Continuity is unnecessary for this equivalence.** The image test may be restricted to nonempty fat basic neighbourhoods contained in the witness, including those with deeper stems. Requiring the images themselves to have interior is stronger than necessary.

The audit does **not** establish that EA2 is necessary for the Ramsey conclusion among all successor-tree monoids. The established equivalence concerns a specified pullback method on one fixed source witness. Further weakening is possible if one changes the desired conclusion, permits witnesses depending on the target set, or strengthens the geometric lifting information. Claims of absolute minimality would therefore exceed the proof.

## 1. Exact local category statement

Let $C$ and $Y$ be topological spaces, and let $q:C\to Y$ be any map. Consider:

1. For every open $O\subseteq Y$, the set $q^{-1}(O)$ has the Baire property in $C$.
2. For every closed nowhere dense $N\subseteq Y$, the set $q^{-1}(N)$ is meager in $C$.

These two conditions are equivalent to the following pair:

1. The inverse image of every Baire subset of $Y$ has the Baire property in $C$.
2. The inverse image of every meager subset of $Y$ is meager in $C$.

### Proof

Every nowhere dense set is contained in its closure, which is closed and nowhere dense. Condition 2 therefore applies to all nowhere dense targets: inverse images preserve inclusion, and subsets of meager sets are meager. If $M$ is meager, choose closed nowhere dense sets $N_i$ such that

$$
M\subseteq\bigcup_{i<\omega}N_i.
$$

Then

$$
q^{-1}(M)\subseteq\bigcup_{i<\omega}q^{-1}(N_i)
$$

is meager. Notice that containment is the appropriate assertion here: an arbitrary meager set need not itself be a countable union of closed sets.

Now let $A$ have the Baire property. Write $A=O\triangle M$, where $O$ is open and $M$ is meager. Inverse images commute with symmetric difference, so

$$
q^{-1}(A)=q^{-1}(O)\triangle q^{-1}(M).
$$

The first set on the right has the Baire property by condition 1, and the second is meager by the preceding argument. Their symmetric difference has the Baire property. Conversely, the two full preservation assertions apply in particular to open sets and closed nowhere dense sets. This proves the equivalence.

No continuity, separation axiom, completeness assumption, or countability assumption on either space is used. In particular, the category argument does not use an unproved topological property of the shape monoid.

The generic statements implementing this reduction are in `SuccessorTree/FatTree/CategoryTests.lean`:

- `nowhereDense_preimage_test_iff_closed`;
- `meagre_preimage_of_closedNowhereDense`;
- `closedNowhereDense_preimage_test_iff_meagre`;
- `baire_preimage_of_open_and_closedNowhereDense`;
- `open_and_closedNowhereDense_iff_baire_and_meagre`.

## 2. Relative and ambient category

The manuscript takes $C=[\mathbf x,\mathbf U]$, an open subset of the fat-tree Ellentuck space $\mathcal R$. EA2 concerns inverse images as subsets of the subspace $C$. The fat-tree theorem is applied to the corresponding restricted subset of $\mathcal R$.

The following fact is slightly more general than the manuscript needs: if $D\subseteq C\subseteq X$ is nowhere dense in the subspace $C$, then $D$ is nowhere dense in $X$. Indeed, if the ambient closure of $D$ contained a nonempty open set $O$, that open set would meet $D$, hence $C$. The nonempty relatively open set $O\cap C$ would be contained in

$$
\operatorname{cl}_C(D)=C\cap\operatorname{cl}_X(D),
$$

contrary to relative nowhere denseness. Thus relative meagerness also implies ambient meagerness, by taking countable unions. This direction does not require $C$ to be open.

If $A\subseteq C$ has the Baire property in $C$, write

$$
A=(C\cap O)\triangle M,
$$

where $O$ is open in $X$ and $M$ is meager in $C$. The preceding paragraph makes $M$ meager in $X$. When $C$ is open, $C\cap O$ is open, and hence $A$ has the ambient Baire property.

There is one inaccurate comment in the original code: the docstring of `baire_image_val_of_isOpen` says that openness of $C$ is essential. **The exact condition for extension of every relatively Baire subset of $C$ to an ambient Baire set is that $C$ itself have the ambient Baire property.** Sufficiency follows from the same proof, because $C\cap O$ is then Baire. Necessity follows by considering the entire subspace $C$, which is open and Baire in itself. For example, every closed $C$ satisfies the extension property, whether or not it is open.

This refinement concerns only the extension direction. Ambient meagerness does not imply relative meagerness in an arbitrary subspace: take $C=\{0\}\subseteq\mathbb R$. The singleton is meager in $\mathbb R$, but the entire one-point subspace is not meager in itself. The original proofs use the valid direction throughout.

At the audited commit, the relevant declarations are `baire_image_val_of_isOpen`, `meagre_of_relative_preimage`, `baire_of_relative_EA2`, and `meagre_of_relative_EA2` in `RelativeCategory.lean`. The restricted pullback is exactly $C\cap q^{-1}(A)$; no regularity is asserted outside $C$.

## 3. A weaker generic geometric condition and the exact fat-witness criterion

Suppose $q:C\to Y$ is continuous and that

$$
\operatorname{int}_Y\operatorname{cl}_Y(q[V])\ne\varnothing
$$

for every nonempty open $V\subseteq C$. Then the two EA2 tests hold.

Open inverse images are open, so they have the Baire property. If $N\subseteq Y$ is closed and nowhere dense, then $q^{-1}(N)$ is closed. Were its interior nonempty, it would contain a nonempty open $V$. But $q[V]\subseteq N$ would force the closure of $q[V]$ to have empty interior, contrary to the displayed condition. Therefore $q^{-1}(N)$ is closed nowhere dense, and in particular meager.

`closedNowhereDense_preimage_of_continuous_and_image` and `open_and_closedNowhereDense_of_continuous_and_image` in `CategoryTests.lean` formalise exactly this sufficient condition. The hypothesis that an image is somewhere dense is written as the negation of `IsNowhereDense`, whose definition says that the closure has empty interior.

The image condition is usually called a skeletal-map condition. This name is not needed in the manuscript: “a set whose closure has nonempty interior” is sufficient. It is strictly weaker than requiring $q[V]$ itself to have nonempty interior. The inclusion

$$
\mathbb R\setminus\mathbb Q\longrightarrow\mathbb R
$$

is continuous. Every nonempty relatively open subset of the irrational numbers has closure containing an interval, whereas its image has empty interior in $\mathbb R$.

There is an exact minimality statement within this continuous-map criterion. For a continuous map, the displayed image condition is equivalent to requiring that inverse images of nowhere dense sets be nowhere dense. The forward implication was proved above. For the converse, if a nonempty open $V$ had nowhere dense image, the inverse image of $q[V]$ would contain $V$ and could not be nowhere dense. If the source $C$ is Baire, one can replace “nowhere dense inverse images” in this equivalence by “meager inverse images”: the inverse image of a closed nowhere dense target is closed, and a closed meager set in a Baire space has empty interior. Thus for continuous maps on Baire sources, the somewhere-dense image criterion is exactly the meager pullback requirement. This is a precise restricted equivalence, not a necessity claim for the full Ramsey theorem.

For general source spaces, the preceding sufficient argument cannot simply replace continuity by Baire inverse images of open sets. Define

$$
q(x)=\begin{cases}x,&x\in\mathbb Q,\\0,&x\notin\mathbb Q.\end{cases}
$$

Every open inverse image has the Baire property: if an open set misses zero its inverse image is countable, and if it contains zero its inverse image contains all irrational numbers and differs from that set by a countable set. The image of every nonempty open interval contains all rational points of that interval, so its closure has interior. Nevertheless

$$
q^{-1}(\{0\})=(\mathbb R\setminus\mathbb Q)\cup\{0\}
$$

is not meager. Thus Baire inverse images of open sets, even combined with the displayed image condition, do not suffice on arbitrary source spaces. **This obstruction does not apply to fat Ellentuck witnesses**, which have the stronger category property proved next.

### Every meager set is nowhere dense on a fat witness

Let $\mathcal R$ carry the fat-tree Ellentuck topology. If $M\subseteq\mathcal R$ is meager, the fat-tree Ellentuck theorem makes $M$ Ramsey null. Consequently every nonempty basic neighbourhood contains a nonempty basic refinement disjoint from $M$. Every nonempty open set contains a basic neighbourhood, so it too contains a nonempty open subset disjoint from $M$.

If $\operatorname{int}_{\mathcal R}\operatorname{cl}_{\mathcal R}(M)$ were nonempty, apply this conclusion inside that open set. The resulting nonempty open refinement would be disjoint from $M$ while contained in its closure. This is impossible: every nonempty open subset meeting the closure of $M$ meets $M$. Therefore $M$ is nowhere dense. The converse holds in every topological space, so meagerness and nowhere denseness coincide in $\mathcal R$.

They also coincide in the open subspace $C=[\mathbf x,\mathbf U]$. A relatively meager subset of $C$ is ambient meager by Section 2, hence ambient nowhere dense by the preceding paragraph. Restricting an ambient nowhere dense set to an open subspace preserves nowhere denseness. Conversely every relatively nowhere dense set is relatively meager.

It follows that every nonmeager Baire subset of $C$ has nonempty relative interior. Indeed, write such a subset as $A=O\triangle M$, with $O$ relatively open and $M$ relatively meager. The set $O$ is nonempty, since otherwise $A=M$. The set $M$ is nowhere dense, so $O\setminus\operatorname{cl}_C(M)$ is a nonempty relatively open subset of $A$. Equivalently, a relatively Baire set with empty relative interior is meager.

### Exact EA2 without continuity

Fix the original fat witness $C$ and the prescribed map $q=\rho_F|_C$. The following are equivalent:

1. The two EA2 tests on $C$.
2. Baire inverse images of every open target set, and

   $$
   \operatorname{int}_{\mathcal M}\operatorname{cl}_{\mathcal M}(q[V])\ne\varnothing
   $$

   for every nonempty relatively open $V\subseteq C$.

For necessity, suppose a nonempty relatively open $V$ had nowhere dense image. Its closure $N=\operatorname{cl}_{\mathcal M}(q[V])$ is closed and nowhere dense. EA2 makes $q^{-1}(N)$ meager in $C$, hence nowhere dense there. But it contains the nonempty relatively open set $V$, a contradiction.

For sufficiency, retain the open inverse-image Baire test and assume the displayed image condition. Let $N$ be closed nowhere dense in the target. Its inverse image $P=q^{-1}(N)$ has the Baire property: the complement of $N$ is open, its inverse image has the Baire property, and Baire sets are closed under complements. If $P$ had nonempty relative interior, that interior would be a nonempty relatively open set whose image lies in $N$, contradicting the image condition. Thus $P$ has empty relative interior, and the preceding subsection makes it meager. This proves the closed nowhere dense test, which is equivalent to the original EA2b by Section 1. No continuity assertion about $q$ is used.

The image condition can equivalently test just the nonempty fat basic neighbourhoods $D\subseteq C$, with **arbitrary deeper stems** allowed. One direction is immediate because such $D$ is relatively open. For the other, every nonempty relatively open $V\subseteq C$ contains a nonempty fat basic neighbourhood $D$. Then $q[D]\subseteq q[V]$, and a set containing a somewhere dense subset is itself somewhere dense. This basis reduction concerns images of source basic sets; it does not justify reducing EA2a to inverse images of target basic opens.

The new module `SuccessorTree/FatTree/FatCategoryCriterion.lean` states these exact conclusions as `fatTree_isMeagre_iff_isNowhereDense`, `fatWitness_isMeagre_iff_isNowhereDense`, `fatWitness_meagre_of_baire_emptyInterior`, `hasRelativeEA2Closed_iff_open_and_image`, `hasRelativeEA2_iff_open_and_image`, and `relativeImage_test_iff_basic`. Its generic core only assumes that every meager source set is nowhere dense. The fat-tree theorem supplies that property; no topological Ramsey or Baire property of the shape-map target is assumed. The new declarations remain subject to the final compilation and transitive axiom gate.

## 4. Strict examples and simplifications that fail

### Generic examples do not establish strictness on a fat witness

Define $q:\mathbb R\to\mathbb R$ by $q(x)=x$ for irrational $x$ and $q(x)=0$ for rational $x$. For every set $A$, the symmetric difference between $q^{-1}(A)$ and $A$ is contained in $\mathbb Q$. Thus inverse images preserve the Baire property and meagerness. The map satisfies both EA2 tests, but is discontinuous at every nonzero point. Moreover,

$$
q^{-1}(\{0\})=\mathbb Q
$$

is meager and dense, so it is not nowhere dense. Thus on general source spaces continuity and nowhere dense inverse images are stronger requirements than the EA2 tests. **The second strictness assertion is false on the actual fat witness:** there every meager inverse image is already nowhere dense, as Section 3 proves. The example does not have a fat Ellentuck source. Likewise, the preceding example showing that continuity cannot be dropped from the generic geometric argument does not contradict the exact criterion without continuity on a fat witness.

### The two tests are independent as topological conditions

For the first direction, let $Y=\{0,1\}$ have the discrete topology and let $A\subseteq\mathbb R$ have no Baire property. Its indicator $q:\mathbb R\to Y$ has meager inverse images of all nowhere dense target sets, because the only such target set is empty. But $q^{-1}(\{1\})=A$ has no Baire property.

For the other direction, a constant map $q:\mathbb R\to\mathbb R$ is continuous and has Baire inverse images of every subset of its target. The inverse image of the closed nowhere dense singleton containing its value is the entire nonmeager source. Thus Baire pullback preservation alone cannot justify the meager/Ramsey-null half of the transfer.

These examples establish independence for the general category lemma. They are not claimed to be successor-tree monoid examples, so they do not establish independence from every geometric consequence of the paper's other axioms.

### Testing only basic open sets is insufficient without further information

Baire sets are closed under countable unions, not arbitrary unions. For example, the identity from the usual real line to the real line with the discrete topology has Baire inverse images of every singleton basic open set. It also satisfies the nowhere dense test, since the discrete target has no nonempty nowhere dense set. An arbitrary target subset is open, however, and a target subset lacking the usual Baire property pulls back to itself. Thus “every open set” cannot safely be replaced by “every basic cone” without a separate countability or union argument. Second countability of the pointwise topology is not a countable-basis theorem for the monoid Ellentuck topology.

### The Baire conclusion alone allows a weaker assumption

If only the Baire/Ramsey half is desired, it suffices to require directly that every Baire target set have a Baire inverse image on the chosen witness. This need not preserve meagerness, as the constant-map example shows. The null conclusion uses the extra category information.

Similarly, when applying the argument to one specified target set $A$, only regularity of that one restricted pullback is required. Uniform EA2 chooses one witness working for all target sets. Allowing the witness to depend on $A$ is a logically weaker sufficient formulation of the transfer method. The theorem does not prove that a uniform witness is necessary.

One may also replace “open” by “regular open” in the first test if the meager inverse-image test is retained: an open $O$ differs from $\operatorname{int}\operatorname{cl}(O)$ by a subset of the nowhere dense boundary of $O$. This is an equivalent reduction of the test class, not a substantive weakening, and introduces terminology without shortening the main proof. The all-open formulation is preferable in the manuscript.

## 5. Common witnesses and pure-depth lifting

Write $C=[\mathbf x,\mathbf U]$ and $d=\operatorname{depth}_{\mathbf U}(\mathbf x)$. The argument needs both regularity of the restricted pullback on $C$ and the cone-covering assertion below the same $\mathbf U$, with the same stem $\mathbf x$. Two unrelated existential witnesses do not supply this conjunction. A common refinement could replace literal equality of the first choices, but existence of an appropriate common refinement would itself need proof.

The audited `HasRelativeEA2` definition, `Section4Conditional.lean` lines 29–44, uses the induced fat-tree topology on this exact $C$. Its target topology is the monoid Ellentuck topology. The two transfer proofs at lines 48–96 and 100–140 use the same $C$ and the same map as the covering hypothesis.

Fat-tree Ramsey homogeneity first gives $\mathbf B\in[\mathbf x,\mathbf U]$. This does not by itself give the pure-depth refinement required by EA1. The declaration `pureDepthRefine_of_basicMember` in `RelativeEA.lean`, lines 32–46 at the audited commit, supplies the necessary step. Fat-tree A3(2) gives

$$
\mathbf V\in[d,\mathbf U],\qquad
\varnothing\ne[\mathbf x,\mathbf V]\subseteq[\mathbf x,\mathbf B].
$$

This is an application of the actual fat-tree amalgamation theorem. It does not assert A3(2) for shape-preserving maps.

For the logical transfer it is enough that every such $\mathbf V$ admit some target pure refinement $F'$ with nonempty target cone $K(F')$ and

$$
K(F')\subseteq\rho[[\mathbf x,\mathbf V]].
$$

The printed EA1 specifies the particular choice $F'=\rho_F(\mathbf V)$. This is stronger than the existential covering hypothesis consumed by the generic Lean proof. The printed equation $F_{\mathbf x}=g$ also gives meaningful geometric localisation but is not used by the abstract category-transfer argument after the covering condition has been supplied. Retaining these source conditions is legitimate; calling the complete formulation logically weakest would not be justified.

At the initial audited commit, `pure` and `cone` in the generic Lean endpoints are arbitrary parameters. Exact source wrappers must instantiate these with the manuscript's genuine monoid depth and composition neighbourhoods, including the empty-stem convention. The new source-facing wrapper work is therefore a substantive correspondence check, not merely a new name for an already literal manuscript theorem.

The exact image criterion in Section 3 clarifies a further quantifier issue. EA1 controls the images of fixed-stem neighbourhoods $[\mathbf x,\mathbf V]$ for pure refinements $\mathbf V\in[d,\mathbf U]$. It does not state the corresponding property for every deeper basic neighbourhood $[\mathbf y,\mathbf W]\subseteq C$. Such a neighbourhood need not contain a neighbourhood with the original stem $\mathbf x$. Reapplying the uniformly quantified EA1 at another target neighbourhood supplies another fat witness; the assertion does not place that witness inside the prescribed $[\mathbf y,\mathbf W]$ or supply a commuting comparison with the original map $\rho_F|_C$. Moreover a fat reduction need not project to a right factor, so the candidate projected target neighbourhood is not automatically available. Thus the tempting derivation of EA2 from EA1 lacks precisely the compatible all-deeper-neighbourhood information required by the exact image test, as well as the open-pullback Baire assertion. This audit proves neither an EA1-to-EA2 implication nor its impossibility; an argument providing that missing compatibility could change the conclusion.

The follow-up audit read the new `SourceTheorems.lean`. Its `SourceEA1Witness` retains the prescribed map $F'=\rho_F(\mathbf V)$, the actual monoid neighbourhoods, and the finite-stem equation. `HasSourceEA` uses `HasRelativeEA2Closed` on that same witness. The numerical depth correspondence is supplied by `source_depth_comp`, `source_depth_comp_iff`, and `source_depth_empty`: for $f=(F\circ G)\restriction_{T({\leq}n)}$, formal depth is $\widetilde G(n)+1$, while the empty stem has formal depth zero. A finite factor supplied by $G$ gives the upper bound. Any factor through a shorter prefix must agree with $G$ on the source nodes, by injectivity of $F$; a node on level $n$ contradicts that shorter bound. This argument is mathematically correct and makes the indexing correspondence explicit. Compilation of the new declarations remains part of the final CI gate.

## 6. Full English proof of the Borel transfer

Let $\pi(\mathbf U)$ be the map carried by an infinite fat tree, and put $\rho_F(\mathbf U)=F\circ\pi(\mathbf U)$. A node $a$ on level $n$ has carried value

$$
\pi(\mathbf U)(a)=(u_n^+\circ\cdots\circ u_0^+)(a).
$$

Later row extensions fix this value because it lies below their source cuts. Thus it is determined by the first $n+1$ rows. A pointwise basic neighbourhood specifies values at finitely many nodes. Choose a bound on their levels; fixing the corresponding finite fat-tree prefix fixes all of these values. This proves product-to-pointwise continuity of $\pi$. No finite-level cardinality assumption is needed for this continuity argument. Left composition by a fixed $F$ is pointwise continuous, since at coordinate $a$ it composes the evaluation with the fixed map on the discrete node set. Hence $\rho_F$ is continuous for the same topologies.

Let $\chi$ be a finite pointwise-Borel colouring. Each colour fibre of $\chi\circ\pi$ is product Borel on fat trees. Every product-open cylinder is fat-tree Ellentuck open: at any member, the basic Ellentuck neighbourhood with that prefix lies inside the cylinder. Hence the colour fibres are Borel, and therefore have the Baire property, in the fat-tree Ellentuck topology.

Fix a nonempty $[\mathbf x,\mathbf U]$. Apply fat-tree Ellentuck successively to the finitely many colour fibres, always retaining $\mathbf x$. Each step gives a smaller nonempty basic neighbourhood contained in or disjoint from the current fibre. If it is contained, stop. If all fibres were avoided, the final nonempty neighbourhood would contain a fat tree having no colour, a contradiction. We obtain $\mathbf B\in[\mathbf x,\mathbf U]$ on whose basic neighbourhood the carried maps have one colour. Fat-tree A3(2), as in the preceding section, gives $\mathbf V\in[d,\mathbf U]$ with a nonempty basic neighbourhood contained in $[\mathbf x,\mathbf B]$. Its carried-map image has the same colour. This proves the unconditional Borel fat-image theorem.

Now assume EA1 and fix a nonempty monoid neighbourhood $[f,F]$. Choose its EA1 witness. Apply the fat-image theorem to the pointwise-Borel colouring $G\mapsto\chi(F\circ G)$. We obtain $\mathbf V\in[d,\mathbf U]$ such that $\chi\circ\rho_F$ is constant on $[\mathbf x,\mathbf V]$. EA1 supplies the required target pure refinement $F'$, the nonempty cone $[f,F']$, and

$$
[f,F']\subseteq\rho_F[[\mathbf x,\mathbf V]].
$$

Every member of this cone has a preimage in the homogeneous fat neighbourhood. Therefore the entire cone has one colour. EA2 is not used in this proof.

The audited `PointwiseBorel.lean` proves coordinate dependence and continuity from the fat Ellentuck topology; `BorelCone.lean` handles the actual relative projection after fixed left composition. `ProductContinuity.lean` separately formalizes the manuscript's product-source continuity assertion; its named endpoints and transitive axioms are included in the mandatory PR #577 certificate.

The follow-up audit also read the new `ProductContinuity.lean`. Its topology is explicitly induced by the sequence of discrete finite approximations. Each carried-map evaluation factors through one approximation via `carriedApprox`; this establishes the required continuity from the product topology, first for $\pi$ and then for $\rho_F$. The argument is correct and supplies the missing exact source-topology statement, subject to the final compilation gate.

## 7. Full English proof of the conditional Ellentuck theorem

Fix a nonempty target neighbourhood $[f,F]$ and choose its common EA1–EA2 witness $C=[\mathbf x,\mathbf U]$. Let $d=\operatorname{depth}_{\mathbf U}(\mathbf x)$.

Suppose first that $A\subseteq\mathcal M$ has the Baire property in the monoid Ellentuck topology. The fixed-map category lemma in Section 1, applied to $\rho_F|_C$, shows that

$$
P=C\cap\rho_F^{-1}(A)
$$

has the Baire property relative to $C$. Section 2 then gives the Baire property in the ambient fat-tree Ellentuck space, because $C$ is open. Fat-tree Ellentuck gives $\mathbf B\in[\mathbf x,\mathbf U]$ such that $[\mathbf x,\mathbf B]$ is contained in or disjoint from $P$. Fat-tree A3(2) gives $\mathbf V\in[d,\mathbf U]$ with

$$
\varnothing\ne[\mathbf x,\mathbf V]\subseteq[\mathbf x,\mathbf B].
$$

All these fat trees lie in $C$. Consequently their $\rho_F$-images all belong to $A$, or all avoid $A$, respectively. EA1 supplies a nonempty target cone $[f,F']$ within that image, with $F'$ a refinement at the required target depth. The entire target cone is therefore contained in or disjoint from $A$. Since the initial $[f,F]$ was arbitrary, $A$ is Ramsey.

If $A$ is meager, the category lemma makes $P$ meager in $C$, hence meager in the ambient fat-tree space. Apply the Ramsey-null half of fat-tree Ellentuck and then the same fat A3(2) step to obtain a nonempty $[\mathbf x,\mathbf V]$ disjoint from $P$. Its members lie in $C$, so their $\rho_F$-images avoid $A$. The nonempty cone supplied by EA1 is contained in this image and therefore avoids $A$. Thus $A$ is Ramsey null. Only the meager inverse-image half of EA2 is used for this last conclusion.

## 8. Source patch review and remaining validation gate

The October 17 patch is mathematically sound after the corrections above. It preserves the manuscript's displayed `$$` mathematics, existing labels, notation and British “colour”. The proof explicitly uses fat A3(2), retains the common witness, distinguishes product, fat Ellentuck and monoid Ellentuck topologies, and uses a countable closed nowhere dense cover rather than incorrectly asserting such a union equals an arbitrary meager set.

Recommended final wording changes are small: use “a bound for their levels” when describing a finite set of coordinates, and explicitly identify the two sets whose symmetric difference is taken in the category proof. A one-sentence proof of relative nowhere dense implies ambient nowhere dense makes the fragile bridge fully self-contained.

The initial proof audit accepts the mathematics independently of CI. Kernel validation is recorded by the exact-head run and the named axiom report linked from PR #577. Those records bind certification to the source commit; concrete EA instances remain separate mathematical tasks.
