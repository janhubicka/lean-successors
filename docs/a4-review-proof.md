# Alternative A4 proof from the paper review

## Verified final checkpoint

At `215baad75a57b43967063b8d33ed8e6989125501`, the focused Review A4
workflow
[37383862698](https://github.com/janhubicka/lean-successors/actions/runs/37383862698)
and the full Lean workflow
[37383862703](https://github.com/janhubicka/lean-successors/actions/runs/37383862703)
both pass.

The focused audit checks **71 transitive theorem-axiom reports**, including
`fixedStemPigeonhole_review` and `ellentuck_review`.  Every report uses
only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx` and no extra A4, saturation, or good-pair premise hidden in the
endpoint.

The abstract Ramsey-space dependency is pinned to merged commit
`bdb601607c03a945bbcd01cfccaa884d4c95e69f`.  Its post-merge CI rerun
[37365422442](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/37365422442)
also passes.  In particular, fusion completeness is obtained from A2 plus
metric closedness before A3/A4 is assembled, so the application proof is not
circular.

## Local simultaneous fan theorem

`A4ReviewReplay.lean` proves the common-tail replay identity using the actual
recorded occurrence of each profile.  Constants retain their recorded edge;
later parameter symbols repeat the genuine first-parameter edge.  This also
handles bottom profile coordinates without identifying successor codes merely
from profile equality.

`A4ReviewForward.lean` proves the forward M2 step.  A raw successor table is
never assumed admissible.  Only an admissible canonical image is used; forward
composition and M2 extract a legitimate one-level letter, and global
saturation shows that its complete profile was already seen.

`A4ReviewFan.lean` and `A4ReviewLine.lean` combine this with the finite
Hales--Jewett theorem.  For every member of a finite trace family and every
raw successor fan whose canonical image is admissible, one common geometric
tail gives the same colour as the corresponding head composite.  The theorem
`exists_reviewFanLine_of_sourceLetter` needs only a one-level letter at the
current cut; the positive-cut wrapper gets this from M3.

## Good-pair linkage

`A4ReviewTransport.lean`, `A4ReviewAlgebra.lean`,
`A4ReviewSplice.lean`, and `A4ReviewWitness.lean` formalize the linkage
which was missing in the first review checkpoint.

Exact-depth persistence first chooses a finite preserved depth.  The
simultaneous fan theorem is applied to every composite of an old exact trace
with an exact bridge to this depth.  The persistent accepted first row is
then factored through the common line head by the **last-block**
factorisation.  Raw successor fans are transported forward through that
factor; associativity identifies the resulting composites, and A3/splicing
reattaches the common tail after the actual accepted head.

`A4ReviewGoodPair.lean` packages this as
`review_goodPair_finite_family_of_sourceLetter` and then as
`review_goodPair_of_sourceLetter`.  The empty exact-trace-family branch is
handled directly.

## Persistence and all-trace fusion

`A4PairPersistence.lean` proves the Baumgartner finite-batch persistence
lemma for a continuation set depending on its first row.  A2 makes every
protected-depth batch finite, A3 lifts each avoidance while preserving the
prefix, and metric closedness supplies the fusion limit.  No use of A4 occurs
in this argument.

`A4ReviewSourceFusion.lean` iterates the good-pair theorem while keeping the
original source cut and accepted colour class fixed.  At every finite prefix
it keeps **all** admissible exact traces from that source cut, and keeps large
the set of next rows good for every one of them.  The fusion predicate
`ReviewStepGood` makes preservation in the limit explicit.

The final coverage uses last-block factorisation, never a first-head
factorisation.  `exists_lastBlock_exactTrace_of_successors` isolates its
true hypothesis: every source-level node has an immediate successor.  A
source letter supplies this also at a moving root.  If no source letter
exists, M3 forces the source cut to be zero and all root rows coincide, so
the one-step front is already homogeneous.

This yields the unconditional theorem

    review_fixedStemPigeonhole

for every finite stem and every colouring of its geometric one-block
extensions.

## A4 and Ellentuck endpoint

`A4ReviewComplete.lean` proves

    fixedStemPigeonhole_review : FixedStemPigeonhole H

and then uses the independently checked A3 transfer in `A4Assembly.lean`
to construct

    abstractRamseySpace_review :
      RamseySpace.AbstractRamseySpace (approximationSystem H)

Finally metric closedness and the audited abstract Ellentuck theorem give

    ellentuck_review :
      RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
        (S := approximationSystem H)

Thus Todorčević A4 and the fat-tree Ellentuck theorem are now
**unconditionally formalized** for the stated SM-tree hypotheses.

The alternative proof does **not** validate the old displayed fat-line
factorisation/equality that motivated the review; it replaces that step by
the simultaneous raw-fan theorem plus all-exact-traces fusion.

## Manuscript annotations

Validation patches should mark the fat-tree A4 proposition and fat-tree
Ellentuck theorem green at commit
`215baad75a57b43967063b8d33ed8e6989125501`.  Review notes should still
explain the replacement proof: fixed-source exact traces, finite-depth
Baumgartner persistence, simultaneous raw-fan Hales--Jewett, last-block
factorisation, and the separate moving-root/root-fixed dichotomy.  Existing
prose that asserts the obsolete first-head factorisation should be corrected
rather than marked as validated.
