# Historical successor v10 validation notes (superseded 14 October 2026)

These are the original cumulative annotation records before the M2 closure. They are preserved for exact provenance, **not** meant to be inserted in the current manuscript. Their OPEN statuses describe intermediate October 11--13 checkpoints, not the current theorem status. The verified normalized M2 and SMTree endpoints are in PRs #379--#381 (integrated by #382).

## Former successor/M1/M2/M3 note

```tex
\todo[inline]{\textbf{v10 validation: the S-tree operation and M1 --
GREEN for the normalized model; language adapter OPEN.}
The exact successor is determined by its complete induced
predecessor, its canonical empty-or-singleton parameter and its
admissible terminal letter. The parameter has the strict required
lower level. Existence for every admissible cover and uniqueness
of the decomposition give the three S-tree axioms in
\texttt{CanonicalCoverS3.lean},
\texttt{CanonicalStepUniqueness.lean} and
\texttt{AdmissibleSigmaSTree.lean}.
For the family of all shape-preserving maps with
$\widetilde F(0)=0$, identity, composition and pointwise fusion
preserve the condition; these maps fix every level-zero node.
See \texttt{ConcreteKptM1.lean}.

\textbf{M3 duplication -- GREEN in the normalized Kpt S-tree;
M2 remains OPEN.}
The finite level-removal construction preserves the forbidden-free
partial structure under the strict guard $\mathrm{fl}(m+1)<m$
and computes the transported free cut
(\texttt{LevelRemovalPartial.lean},
\texttt{LevelRemovalFreeCut.lean}).
The checked \texttt{LevelRemovalType.lean} proves that the complete
$L^+$ type of a retained vertex is precisely the old type
with coordinate $m$ deleted, including absent directed tuples,
singleton/diagonal information and every $E$ pair (PR~267).
The additional \texttt{LevelRemovalAdmissibleType.lean} derives
the new canonical free level and constructs an actual
$\mathcal F$-free witness of this coordinate-deleted complete
Kpt type (PR~269, full Lean 38174237646 and focused named-axiom
audit 38174237715 both GREEN). These remain \emph{local}
ingredients: the uniform level-removal shape map and M2
decomposition have not been proved. In particular, at the
source boundary level $n$ of the intended global deletion,
the image has no ordinary coordinate
$m+1=\widetilde F(n)$ in its socle yet.
\texttt{LevelRemovalSourceSuccessor.lean} proves from the
checked universal M3 law that every positive-level Kpt node
admits a genuine successor, with actual parameters and letter
(PR~273, full/focused Lean GREEN).
\texttt{LevelRemovalGapColumn.lean} then shows that when
$\ell(F(q))+1<\ell(F(a))$ for the preceding source level,
each parameter of a genuine successor of $a$ maps strictly
below $m=\ell(F(a))-1$, and the genuine \emph{weak} image
successor has a valid ordinary E-column with cut $f<m$
(PR~272, full/focused Lean GREEN).
The weak successor is below the later image, not necessarily
equal to that image. The exact free E-cut transfers through
complete $L^+$ prefixes to \emph{every} actual finite
representative of an upper image
(\texttt{LevelRemovalWitnessCut.lean} and
\texttt{LevelRemovalPrefixCut.lean}, PRs~274, 276, GREEN).
\texttt{LevelRemovalGapSeparation.lean} and the
verified source-level comparison (PR~281) show the
coordinate $m$ is genuinely omitted by $F$.
The checked uniform image guard and admissible shortened
prefix were integrated in PR~283, and
\texttt{LevelRemovalBoundaryAdmissible.lean} proves that
the \emph{intrinsically specified} deleted complete $L^+$
image is admissible both at the source boundary and above
a chosen actual successor (PR~285, GREEN).
The successor and finite witness are used only to prove
membership, not to choose the deleted value.
The full \emph{all-level} admissibility consequence is now
checked in \texttt{LevelRemovalAllLevelsAdmissible.lean}:
the deleted complete raw record of $F(x)$ belongs to Kpt
for every source $x$ at or above the boundary level,
across every tree component, using one fixed deletion
coordinate $m$ (PR~287, exact head \texttt{68069ab3},
full Lean run 38195482771 and focused transitive axiom
run 38195482724 GREEN). The intrinsically specified total deletion, strict level function
and full prefix order have been integrated in PR~299, with the
canonical empty-or-singleton parameter transport integrated in PR~305.
The checked sharp upper-step safety is recorded in PR~309.
The four component proofs and sharp guard are integrated in PR~306;
PR~310 proves the remaining high-base weak successor, and PR~311
packages the complete intrinsic deletion as a root-preserving Kpt
ShapeMap, deriving injectivity from weak successors.
The exact-head full and focused named-axiom runs passed for PR~306
(38253790327/38253790321), PR~310 (38250692961/38250692981)
and PR~311 (38252865811/38252865671), each with standard axioms.
These normalized local facts are GREEN; the complete M2
factorization remains OPEN.

For M3, the actual gated finite middle-clone insertion satisfies
the corrected $L$-only age test and yields one ShapeMap in $K_{pt}M$
skipping only $\ell$ (PRs~253, 258--259).
\texttt{M3RepresentativeIndependence.lean} proves independence
of the chosen finite witness, and
\texttt{M3LiteralDuplication.lean} proves the complete universal
duplication law for every earlier admissible successor and the
same parameter list and letter (PR~266).
All new endpoints passed full builds and named transitive axiom
audits with standard Lean axioms. The identification with the
original unary/binary language is a separate OPEN adapter.}
```

## Former prescribed boring-extension and M2 note

```tex
\todo[inline]{\textbf{v10 validation: boring extension -- GREEN in the
normalized finite unary/binary model; M3 GREEN, M2 and
language adapter OPEN.}
The repaired B3 quantifies over finite ordered $L$-structures with the
ordinary socle of a prescribed $f(S)$ and complete upper $L$-types
through $\ell+1$ from the reducts of $f[S]$. If deleting $\ell$ leaves an $\mathcal F$-free structure, the whole
structure must be $\mathcal F$-free. No auxiliary $E$ requirement belongs on these
age-test witnesses. The former $E$-expanded upper-tail condition cannot
serve this purpose: spacing excludes the first required upper vertex;
without a prescribed initial socle the empty upper tail is also invalid.
The localized mathematical repair was applied to the previously supplied
V10 source; its provenance is recorded in
\texttt{v10-b3-author-source-check-20261010.md}.
This annotation updater does not reapply or alter that repair.

\textbf{Finite prescribed construction -- GREEN in the normalized model.}
\texttt{PrescribedCorrectedB3.lean} derives the finite common-socle
age test from the corrected manuscript condition and supplies a genuine
forbidden-free prescribed insertion. The upper columns and their linkage
conditions are derived from $f$, not assumed independently.
All old $L^+$ atoms, including absent directed tuples, are preserved.
\texttt{PrescribedETransport.lean} checks the new $E$ row, new column,
old pairs and loop for an arbitrary valid inserted cut; this is not
restricted to the neutral branch.
\texttt{PrescribedSourceRecovery.lean} recovers each shorter ordinary
source type from the complete longer record.
These statements were checked at the PR~203 checkpoint, including the
transitive axiom audit. The allowed neutral branch and its full
\texttt{ShapeMap}, exact skipped level, predecessors, injectivity,
terminal letters and empty-or-singleton parameters are also checked.
At the unique edge from $\ell-1$ to $\ell$, use the weak successor
statement, not equality with the shifted target. The assumption $\ell>0$
remains essential for the finite $E$ insertion.

\textbf{Prescribed representation independence -- GREEN
for the finite constructor.}
\texttt{PrescribedIncidentIndependence.lean} derives the gate
$\ell\leq\freef A(u)$ from the source atom $E(\ell-1,u)$, and recovers
shorter source types at ordinary and distinguished coordinates.
It proves that source compatibility, the selected lower column and
both gated incident directions are independent of the ambient witness.
\texttt{PrescribedRecordIndependence.lean} combines these identities
with exact transport to compare the entire inserted $L^+$ record,
including every positive and absent binary atom, singleton fact and
$E$ pair. Its final endpoint compares the actual finite prescribed
constructors for two ambient realizations and two compatible prescribed
outputs. Equality of the inserted cuts is derived from their common
ordinary socle, not added as a hypothesis. The focused builds and
transitive axiom audits for PRs~205 and~206 passed. All nine new
endpoints use only standard Lean axioms; the downloaded evidence
was checked. This is not a global shape-map theorem.

\textbf{Admissible prescribed images and total node map --
GREEN in the normalized model.}
\texttt{PrescribedMatchingFinite.lean} now retains the actual
\texttt{prescribedInsertPartial} constructor and its inserted cut in
its witness-existence conclusion. The earlier existential theorem is
only a corollary; its hypotheses are unchanged and the construction
is not duplicated. \texttt{PrescribedAdmissibleImage.lean} obtains a
forbidden-free admissible image at level $n+1$ from corrected B3 and
admissibility of the prescribed targets. Its image relation is proved
functional for different ambient structures and different compatible
source representatives. Equality of the cuts and lower columns still
comes from B2, not an extra compatibility assumption.
\texttt{PrescribedKptSkip.lean} combines this unique matching image
with the already checked neutral image, fixing all nodes below $\ell$.
The compatibility test is made on the node's own complete prefix.
The resulting candidate is total on the actual admissible node set;
its level is $n$ for $n<\ell$ and $n+1$ for $n\geq\ell$.
The branch specifications, omission of level $\ell$, preservation of
equal levels and strict increase of numerical levels are explicit
endpoints. These numerical facts are not node injectivity or tree-order
preservation. The exact-head focused builds and transitive axiom audits
for PRs~208 and~209 passed. The fifteen new endpoints and the retained
existential API were checked in downloaded audit artifacts; all use only
standard Lean axioms. This does not certify the prescribed shape map.

\textbf{Prescribed old-record recovery and injectivity -- GREEN.}
\texttt{InsertedTypeRecovery.lean} defines deletion of the inserted ordinary
coordinate on complete raw $L^+$ records. All retained coordinates,
including the distinguished vertex, keep their positive and absent
binary atoms, unary and diagonal facts, and every $E$ pair.
\texttt{PrescribedKptInjective.lean} uses the same deletion for prescribed
and neutral images and fixes raw nodes below $\ell$. Its left-inverse
identity recovers the original raw node from the actual total candidate.
This proves injectivity also for comparisons between prescribed and
neutral images, without assuming predecessor preservation or equal
branch choices. No new hypothesis on the total map is added.
Deletion is defined on raw records; admissibility of its value on an
arbitrary admissible input is not asserted. On the candidate's image,
its value is the original admissible node.

\textbf{Computation in any finite representative -- GREEN.}
\texttt{PrescribedImageRepresentation.lean} identifies any supplied valid
inserted cut with the cut obtained from finite existence, using the
uniqueness of the ordinary $E$-column. Thus the literal constructor at
that cut is forbidden-free; its avoidance is derived rather than added
as a premise. The selected matching image can consequently be computed
in any forbidden-free finite representative of its source, using any
compatible prescribed source and valid inserted cut. This supplies the
representation adapter for the prefix-replica argument; it is not itself
a proof of predecessor preservation. The exact-head focused builds and
transitive axiom audits for PRs~211 and~212 passed. All twelve new
endpoints use only standard Lean axioms; the downloaded evidence was
hash-checked and the named-endpoint checker was rerun.

\textbf{All prescribed predecessors -- GREEN.}
\texttt{PrescribedKptPrefixCases.lean} derives equality of the complete
level-$\ell$ restrictions along every upper chain, and therefore equality
of the compatibility decisions. No extra same-branch hypothesis is used.
\texttt{PrescribedKptPrefixMatching.lean} represents the shorter source
by the existing one-filler prefix replica. Both selected images can then
be computed with the same compatible prescribed source and inserted cut;
full-record independence identifies the shorter image with the appropriate
prefix of the longer one. The unmatched case uses the neutral theorem.
\texttt{PrescribedKptFullPrefix.lean} handles crossing the gap using only
retained old atoms. Its lower-prefix statement also covers the source
itself at level $\ell$; this is a predecessor statement, not agreement
with $f$. All source predecessor relations are consequently preserved.

\textbf{Exact predecessor transport and order embedding -- GREEN.}
\texttt{PrescribedKptOrderEmbedding.lean} identifies the image of the
actual admissible predecessor at level $n$ with the predecessor of the
image at level $n$ if $n<\ell$, and at level $n+1$ otherwise.
This follows from the full predecessor theorem, the level formula and
uniqueness of a predecessor at a fixed level. Conversely, if two images
are comparable, take the predecessor of the longer source at the shorter
source's level. Its image and the shorter image have the same level and
lie below a common image, hence coincide. Injectivity identifies their
sources. Thus the concrete map preserves and reflects the prefix order,
and is packaged as an order embedding. This argument uses admissible
prefix closure, not admissibility of arbitrary coordinate deletion.
The four new endpoints and ten inherited prefix endpoints passed the
focused build and named axiom audit at PR~219. The downloaded artifact,
exact new source and check-script bytes were verified; all reports use
only standard Lean axioms. The source tree of the tested synthetic merge
agrees with the committed proof head.

\textbf{Weak successors below and across the gap -- GREEN.}
\texttt{PrescribedKptGapSucc.lean} first proves that every source at
level $\ell$ is a complete predecessor of its prescribed-or-neutral
image. If a successor base lies below $\ell$, the actual S-tree axiom
puts all its parameters below the base, so both the base and its
parameter list are fixed. The old successor then witnesses the weak
mapped-successor condition: it is fixed if its level is below $\ell$,
and is a predecessor of its image if its level is exactly $\ell$.
This includes the boundary from $\ell-1$ to $\ell$ without asserting
equality with the shifted image. No above-gap parameter or terminal-letter
identity is assumed in this argument. Both new endpoints passed the
focused build and named axiom audit at PR~222; the downloaded source,
check-script bytes and standard-only axiom reports were verified.

\textbf{Suggested clarification of the construction.}
Choose a finite $\mathcal F$-free partial structure representing the
source type. Use the prescribed finite construction when its ordinary
socle is compatible with a prescribed source, and the neutral
construction otherwise. Take the complete type of the retained
distinguished vertex at its transported free level. The full
$L^+$-record independence, rather than just equality of the lower
column or of the $L$-reduct, makes this definition independent of
both choices. To see injectivity, delete the inserted ordinary coordinate
and shift the retained ordinary coordinates back. This recovers the
complete source type in both branches, while nodes below $\ell$ are fixed.
For comparable upper sources, their level-$\ell$ restrictions agree.
In the matching case, compute the shorter image using the one-filler
prefix replica of the longer representation; record independence gives
the required predecessor. In the unmatched case use the neutral
construction. Below the gap only retained old atoms occur. This proves
all predecessor cases, including crossing the gap.

\textbf{Prescribed source values and finite successor inputs -- GREEN.}
\texttt{PrescribedSourceFullValue.lean} proves that the selected total
node map agrees with $f$ on every admissible source in its domain,
as equality of the COMPLETE $L^+$ type, not merely the $L$-reduct.
\texttt{PrescribedTerminalLetter.lean} transports every positive and
absent directed $L$ atom, all singleton data and the $E$ atoms of the
terminal letter through the actual prescribed insertion.
\texttt{PrescribedOldParameter.lean} computes the chosen total
map at each retained old vertex of the prescribed finite model and
therefore transports the canonical empty-or-singleton parameter list.
The full Lean and focused named-axiom audits of PRs~218, 223 and 224
passed independently with unchanged corrected-B3 assumptions.

\textbf{Complete prescribed one-gap ShapeMap -- GREEN
for the normalized model.}
\texttt{PrescribedUpperSuccMatching.lean} uses one genuine finite
prescribed insertion and the checked exact parameter/terminal-letter
transport to prove successor equality above the gap.
\texttt{PrescribedUpperSuccUnmatched.lean} identifies the source, target
and canonical parameter with their neutral images when the common
ordinary level-$\ell$ socle has no compatible prescribed source.
\texttt{PrescribedKptShapeMap.lean} combines both upper cases with the
weak below/crossing successor law, full predecessor and injectivity
theorems, and root fixing. It constructs the actual
\texttt{ShapeMap} in $K_{pt}M$, omitting level $\ell$.
\texttt{PrescribedBoringCompletion.lean} uses the independently verified
nonempty Kpt levels and the explicit level map to obtain the stronger
\texttt{SkipsOnly} conclusion. It packages membership in $K_{pt}M$,
exact omission of $\ell$, and complete $L^+$ agreement with $f$ into
\texttt{prescribedKpt\_boring\_extension\_exists}.
The exact-head focused builds and named transitive axiom audits of
PRs~226 and~227 passed with standard Lean axioms only. The new
public-root import of this endpoint is staged separately in PR~228
so ordinary \texttt{lake build} cannot silently omit it.
No new mathematical hypothesis or abstract successor-preservation
axiom was introduced. This certifies the normalized-model version of
Lemma~\ref{lem:boring}, conditional on corrected B3; it does not
certify the original-language identification or its applications.
For M2, the former third statement of Lemma~\ref{lem:comp} does not
imply the strengthened B3: it treats enumerated $E$-partial structures,
while corrected B3 quantifies over arbitrary finite ordered $L$-age
witnesses. In particular, adding neutral separators to lift an
$L$-witness need not put the separators in the original map's image,
and distinct upper $L$-columns need not have compatible ordinary
$E$-socles. Formalize either a selected-upper/weak age-transport lemma
with these two issues resolved, or a direct one-level factorization
that avoids inferring corrected B3 from the old third statement.
A staged conditional reduction (\texttt{LevelRemovalM2Criterion.lean},
PR~312) takes corrected-B3 prescribed insertion data and an exact
boundary-level agreement with the intrinsic deletion factor, then
derives the required composition equality at \emph{all} earlier
source levels: below the boundary the deletion factor is literally
$F$ and the prescribed map is literally the identity beneath its
one omitted target level. PR~312 passed exact-head full Lean run 38253923339, focused
named-axiom audit 38253923143 and manuscript validation.
It does not construct the prescribed data or establish corrected-B3
age necessity from $F$.
The subsequent exact-extension reduction isolates a weaker open task:
extend the well-defined boundary prescription
$D(x)\mapsto F(x)$ to an arbitrary one-gap Kpt ShapeMap.
Lower-level agreement can be derived without corrected B3 or M2,
provided one first establishes identity below a unique skipped level
directly from the Kpt level-range formula and weak successors.
The M2-independent lower-identity and arbitrary one-gap
boundary-extension equivalence are GREEN in PR~313, which passed
full Lean 38268558208 and focused transitive axiom audit
38268558200 and has been merged. No M2 is assumed.
PR~314 constructs the partial restoration graph on the actual deleted
boundary image $D[K_{pt}(n)]$: by injectivity of $D$, the prescription
$D(x)\mapsto F(x)$ is a well-defined function, with input level $m$ and
output level $m+1$ across all tree components. PR~314 passed full Lean
38268563188 and focused standard-axiom audit 38268563272 and was merged.
The remaining task is to extend this partial function to a one-gap
Kpt ShapeMap; its finite age/compatibility requirements have not
been proved.
PR~315 is GREEN: deleting the final ordinary coordinate from a
complete $L^+$ type equals its full predecessor restriction,
including all directed, singleton and auxiliary $E$ data, and the
actual intrinsic boundary deletion is this same predecessor of $F(x)$.
The exact-head full Lean 38270726577 and focused standard-axiom
audit 38270726588 passed and the PR was merged. This verifies B1,
but does not imply B2 or corrected finite $L$-age necessity.
A direct finite-age alternative is staged in PR~316: if the new
ordinary vertex is $L$-linked to at most one designated upper vertex
and the induced $L$-structure on the initial socle plus that vertex
is forbidden-free, then binary irreducibility rules out every
forbidden copy involving the inserted coordinate. Copies avoiding
it project back to the old age. This one-linked-upper age theorem passed exact-head full Lean
38270821103 and focused standard-axiom audit 38270821068,
and was merged as PR~316. It does NOT construct the insertion or
prove the one-link condition for the desired global map.
In fact, canonical parameter transport may force the inserted
vertex to be linked to several upper vertices simultaneously;
thus the one-linked lemma is NOT a substitute for corrected B3
without an additional compatibility invariant.
A possible next step for B2 is to free-amalgamate two compatible
source types over their common ordinary socle, and use an actual
mapped successor whose canonical parameter is the second type
to compare their inserted ordinary columns. This is a proposed
argument only, not yet validated. The finite L-only age test
with several linked upper vertices remains OPEN.
PR~317 defines the unique partial restoration $R(D(x))=F(x)$
on the entire image of $D$, with the exact one-gap level function:
below $m$ the level is fixed and at or above $m$ it increases by one.
This stronger partial result passed exact-head full Lean 38271325042,
focused standard-axiom audit 38271325092 and TeX annotation checks
on its original branch; the proof is restaged byte-identically here
for integration testing. It does not give a total ShapeMap outside
$D[K_{pt}]$, and the multi-upper age and successor conditions remain OPEN.

PR~318 proves that shape-preserving maps also reflect the
complete predecessor order, using injectivity and uniqueness of
ancestors. Thus the partial restoration $R$ on $D[K_{pt}]$
preserves and reflects prefix order and is injective; it is an
order embedding of its partial domain. This proof passed full Lean
38272059762, focused standard-axiom audit 38272059862 and TeX
checks on its original exact head, and is restaged with the same
mathematical proof blobs for cumulative integration.
Order embedding alone neither extends $R$ to all Kpt types nor
supplies the missing successor and multi-upper age conditions.


\textbf{13 October 2026 M2 checkpoint: B2 transport GREEN, B3 OPEN.}
The joint non-edge-padded source construction for two complete,
ordinary-compatible admissible types was checked and merged in
PR~357. Applying a genuine shape-preserving map to this single
source witness yields compatible complete ordinary image socles.
Full retained-record recovery also \emph{reflects} compatibility
through any genuine shape map, including intrinsic deletion.
The resulting general compatibility transfer theorem
\texttt{shapeMap\_transfers\_ordinary\_compatibility}
was checked and merged in PR~358. It includes all directed absent
atoms, singleton data and the auxiliary E matrix. These GREEN
statements supply the difficult transport part of boundary (B2),
but the complete boundary \texttt{PrescribedBoringData} declaration
still needs construction.
For the multi-upper (B3) proof one must preserve the \emph{actual}
upper--upper atoms of a putative forbidden copy, not replace these
upper pairs by non-edges. The checked sparse pullback and neutral
completion provide the source finite age. A new explicit
real-vertex atom interface and the review-only proof analysis are
staged in \texttt{M2BoundedCopyRecords.lean} and
\texttt{v10-M2-nonedge-finite-age-appendix-review-20261013.tex};
until exact-head CI passes, neither is a GREEN marker.
The remaining genuine gap is the simultaneous source-type recovery
and induced forbidden-copy comparison inside a single image F(C),
needed to establish compatible B3 and hence (M2).

This M2 obligation remains OPEN.

\textbf{M3 duplication -- GREEN in the normalized model;
original-language identification OPEN.}
For every $n<\ell$, the actual $E_3$-gated finite clone produces
a prescribed $f$ on \emph{all} admissible level-$\ell$ source types.
The corrected B3 finite $L$-age test follows from the linked-only
irreducible projection, without requiring $E$ on an arbitrary age
witness and without imposing one free cut on incompatible sources.
The one-gap ShapeMap agrees with this prescribed $f$ and skips
precisely $\ell$.
\texttt{M3RepresentativeIndependence.lean} identifies the complete
target $L^+$ type for any two finite representatives of the same
source, including every $E$-atom.
\texttt{M3LiteralDuplication.lean} proves the literal universal
(M3) condition: from any $S(a,\bar p,c)\preceq b$ with $a$ at
level $n$ and $b$ at level $\ell$, the \emph{same} map satisfies
$\Phi(b)=S(b,\bar p,c)$. This uses uniqueness of the earlier
level-$(n+1)$ predecessor and S2 to identify the full parameter
list and terminal letter; no successor or M3 axiom is added.
Full Lean, focused named-axiom and source-annotation CI passed
at PR~266, exact head \texttt{2d7f26f3} (runs 38173146352,
38173146346, 38173146351). This certifies the complete normalized
Kpt version of M3, not the unperformed original-language adapter.

The finite guarded type-deletion transport
\texttt{LevelRemovalType.lean} passed full/focused CI at PR~267,
exact head \texttt{9b62b29e}. Its successor
\texttt{LevelRemovalAdmissibleType.lean} proves that deletion
of coordinate $m$ from the complete type of a genuine
forbidden-free witness $v$ with $m<\mathrm{fl}_A(v)$ is itself
an admissible Kpt type, represented by $v-1$ with free level
$\mathrm{fl}_A(v)-1$ (PR~269, head \texttt{9cfbd5f1},
full Lean 38174237646, focused audit 38174237715 GREEN).
At the boundary of a uniform deletion map, however, the
ordinary coordinate $m+1$ is absent from the level-$n$
image type. The checked \texttt{LevelRemovalSourceSuccessor.lean}
(PR~273) uses M3 without M2 to supply a genuine successor
of each positive-level source type.
The checked \texttt{LevelRemovalGapColumn.lean} (PR~272)
derives a valid target successor column with strict E
free cut $f<\ell(F(a))-1$ from the source gap and S1;
the output is only required to lie below the source
successor's image. The transfer of this bound into \emph{every} representative
of a later image and the admissibility of a shorter
complete deleted prefix are now proved in PRs~276 and~283,
respectively. PR~285 verifies admissibility of the
intrinsically specified deleted image at the boundary and
above a genuine successor; witnesses certify membership
but do not choose the output.
\texttt{LevelRemovalPrefixCommute.lean} (PR~277) and
\texttt{LevelRemovalRawPrefix.lean} (PR~280) prove
complete $L^+$ prefix order preservation when both
cuts exceed the deleted coordinate.
\texttt{WeakSuccessorInjectivity.lean} (PR~284)
derives injectivity \emph{conditionally} from strict
level ordering, root extension and the genuine weak
successor law; it cannot be invoked before that law
is proved for the uniform deleted map. Complete cross-gap prefix compatibility is verified in
\texttt{LevelRemovalCrossGapPrefix.lean}
(PR~286, exact head \texttt{5172a0f2}, full Lean
38194440667 and focused 38194440660 GREEN).
The all-level intrinsic deletion \emph{membership} is
verified in PR~287. The intrinsic function and strict level/order
laws have been integrated in PR~299, and the unified canonical
parameter transport in PR~305. PR~306 assembles the genuine
low/crossing weak-successor components; PR~310 proves the upper case,
and PR~311 gives the intrinsic global ShapeMap. All three merged after
successful exact-head full builds and focused transitive axiom audits.
The first global M2 deletion factor is GREEN in normalized Kpt.
\textbf{Genuine crossing weak successor -- GREEN locally.}
\texttt{LevelRemovalBoundaryWeakSucc.lean} (PR~292,
full Lean 38196554700 and focused 38196554661 GREEN)
proves that the actual weak successor at the first gap
lies below the complete coordinate-deleted upper image,
without asserting equality across the skipped level.
\textbf{Complete terminal letter -- GREEN locally.}
\texttt{LevelRemovalTerminalLetter.lean} (PR~293,
full Lean 38196947662 and focused 38196947688 GREEN)
proves that deletion of an earlier ordinary coordinate
preserves the entire terminal $L^+$ Sigma letter.
\textbf{Complete canonical predecessor parameter -- GREEN locally.}
\texttt{LevelRemovalParameter.lean} (PR~295,
full Lean 38197151180 and focused 38197151194 GREEN)
shows that the last-ordinary parameter is deleted
at its own socle if $m<f$, and otherwise is unchanged.
It includes all positive and absent directed tuples,
singleton values and auxiliary $E$ atoms.
The Option-valued empty-or-singleton parameter adapter
(PR~297) and canonical E-column validity (PR~296) have
subsequently passed their respective checks and were integrated.
The local deletion proof no longer needs an auxiliary successor
axiom: PR~309 derives the sharp $m<k$ or $f<m$ guard
from the actual mapped upper canonical step. PR~310 assembles
the missing high-base weak-successor proof from the complete
deleted record and admissible deleted weak target; PR~311 constructs the intrinsic function as a genuine ShapeMap,
deriving injectivity from strict levels, root extension and weak
successors.
It also records literal agreement below the source gap and
the recovery of the skipped target level by the deletion factor.
\textbf{Status: global deletion ShapeMap GREEN (PRs~310--311).}
The complementary one-gap map, and the existence of an extension
realizing $F$ at every boundary source type, remain OPEN.
The corrected-B3 finite $L$-only age necessity is still required
for the prescribed-extension route, but the exact-extension
criterion does not assume it.
Do not conflate constructing the first factor with proving (M2).
Finally, reconcile the I3 signature witnesses with finite
$L$-structures rather than $E$-partial structures before claiming
the upper bound.}
```
