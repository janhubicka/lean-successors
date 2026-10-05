# Alternative A4 proof from the paper review

## Verified checkpoint

At `10d0f5fcd92ccd98cb8284b33860bfdfabbfdd36`, the Review A4 workflow
[37359516130](https://github.com/janhubicka/lean-successors/actions/runs/37359516130)
passed its proof build and all **32 transitive axiom reports**. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. The local fan-line
existence theorem assumes neither A4 nor a saturation/pigeonhole principle.
Its positive-cut form follows from the SM-tree axioms and the already
formalized finite Hales--Jewett theorem.

The default library now imports `A4ReviewLine.lean`, so the common-tail,
forward-M2, and raw-fan colour theorems are included in the full build too.
This is not yet an unconditional certificate for the whole A4 theorem:
`ReviewGoodPairPrinciple` remains an explicit hypothesis of the separate
global fusion endpoint.

## The local combinatorial theorem is now proved

`A4ReviewReplay.lean` proves the pointwise common-tail identity. Constants
use their original recorded occurrence; later parameter symbols repeat the
actual first-parameter edge. The induction keeps that first-parameter
endpoint as an ancestor of the current point. This proves the identity at
EVERY trace coordinate, including bottom coordinates. No equality between
two bottom profiles is used to identify successor codes.

`A4ReviewForward.lean` proves the forward-M2 representation step. A raw
successor table e is not assumed admissible. Suppose only that its canonical
image theta = h^+ e is admissible. Choose one recorded profile and transport
its replay letter through the current ambient row. Call the resulting
letter C. It skips only the image level of h, and C h agrees on the trace
images with the next reachable history state. The FORWARD composite C theta
is admissible. Its predecessors at the next cut are the corresponding
history points. M2 extracts a one-level letter realizing this successor
image. Since this is a finite continuation of the globally saturated
collector, its full profile was already seen. The desired raw fan occurs
at its selected coordinate.

The auxiliary theorem `review_letter_for_admissible_successors` formalizes
this extraction without requiring the predecessor table itself to be an
M-map. The source cut may be zero in this auxiliary theorem. Neither the
raw table nor a pullback of an admissible map is silently declared admissible.
Using a transported replay letter instead of a separately identified total
duplication map simplifies the review's forward argument without changing
its action on the relevant trace images.

`A4ReviewFan.lean` closes the common tail with the final ambient row and
proves equality of actual admissible approximations with the evaluated
Hales--Jewett words. The vector colouring therefore yields, simultaneously
for all traces q and all admissible canonical raw-fan images theta = h^+ e,

    chi(h' theta) = chi(h q).

The hypotheses do NOT restrict raw e to admissible letters. In the intended
all-trace update, theta is already an admissible exact trace, so this form
avoids an unnecessary extra truncation of the final composite.

`A4ReviewLine.lean` constructs the saturated history and the nonempty
alphabet and packages the result as `ReviewFanLine`. The head and the common
tail have geometric stem certificates inside the ambient fat tree; their
middle cuts agree. The tail is certified over the whole ambient middle
level, not only over the finitely many trace images.

The theorem `exists_reviewFanLine_of_sourceLetter` requires just one
admissible letter at the initial ambient cut. The theorem
`exists_reviewFanLine_positive` obtains that letter directly from M3 at a
positive cut. Thus the local simultaneous fan construction is no longer a
postulated lemma. The root-moving zero-cut version can use a root letter;
the root-fixed case is treated separately by the existing root lemmas.

## The global persistence and fusion are also proved

`A4PairPersistence.lean` proves `persistentAcceptedPair_of_dense_pairs` for
an accepted continuation set depending on its first block. If every
stem-preserving refinement contains an accepted pair, there is an accepted
head with a large accepted continuation below a literal realization.

The proof replaces the review's global enumeration by finite batches at
preserved depths. A2 makes the batch finite. A3 lifts an avoiding refinement
below each head to an ambient refinement preserving the whole current
prefix. If every batch can be eliminated, metric closedness gives a fusion
limit. Any good pair in that limit has its first block at an exact depth d;
that head was in the depth-d batch and its second block was eliminated.
This contradiction proves persistence. The argument does not use A4.

`A4ReviewFusion.lean` implements the fixed-source all-trace invariant. Keep
the original source cut c, initial height n, and accepted set O fixed. At a
current prefix y, retain ALL admissible exact traces from c through y. The
large set at y consists of rows h for which every composite hq belongs to O.
The verified exact-trace update identifies the accepted continuation set.
Pair persistence selects h while keeping the whole updated set large.
Dependent recursion and closed fusion construct the infinite reduction.

The finite-prefix predicate `ReviewStepGood` makes preservation in the
limit explicit. Last-block factorization, not a first-head factorization,
then covers arbitrary geometric one-step extensions at a positive original
source cut. The endpoint `review_fixedStemPigeonhole_positive` is proved
from `ReviewGoodPairPrinciple`; when O is not large, immediate avoidance
supplies the other colour alternative.

## Exact remaining proof boundary

`ReviewGoodPairPrinciple` is a definition of the local large-set
`trace-good-pair` statement, not a theorem or an axiom. Its derivation from
the now proved simultaneous fan-line theorem still needs to be integrated:

1. Apply exact-depth persistence to the current large good-row set. Form
   the finite composite trace family {p q}, with p running over the exact
   traces to the preserved depth and q over the original prefix traces.
2. Apply `exists_reviewFanLine_positive` (or the source-letter form) to
   this family. Use the persistent large-set witness to select the first
   block through the constructed head, and use last-block factorization.
3. Transport each raw trace update through that factorization and splice
   the common second block geometrically after the selected first block.
   The simultaneous fan-colour theorem then supplies the complete updated
   trace-good condition, not merely the condition on the last selected head.

The empty composite-family case must be handled explicitly. The
root-moving original-source-cut-zero coverage also needs the existing
last-block factorization generalized to use successors supplied by a root
letter instead of positivity. The root-fixed case is already handled by
`A4RootPigeonhole.lean`.

Once these steps prove the local good-pair principle and zero-cut coverage,
the checked global fusion, A3 transfer, metric closedness, and the audited
abstract Ellentuck endpoint provide the final theorem. Do not mark A4 or
the fat-tree Ellentuck theorem unconditional before that linkage is checked.
In particular, none of this certifies the old displayed fat-line equality
in `lem:4andy`, which the alternative proof deliberately avoids.

## Manuscript annotations

`manuscript/a4-review-validation.tex` supplies isolated validation/TODO
macros. The finite-batch note belongs at `lem:fixlevel`. The simultaneous
raw-fan replacement note belongs at `lem:fatpigeonhole1`, not as a validation
of the false preceding fat-line equality. The all-trace note belongs at
`prop:A4`. These annotations preserve the manuscript's original prose and
its existing `validation.tex`; they record both the new certificates and
the remaining local-to-global obligation.
