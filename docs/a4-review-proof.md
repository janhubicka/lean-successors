# Alternative A4 proof from the paper review

## Verified checkpoint

At `01b40dbe3495fc655e8f9b5f3400aafed86415da`, the Review A4 workflow
[37354774029](https://github.com/janhubicka/lean-successors/actions/runs/37354774029)
passed its build and all 14 transitive axiom reports. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The argument does not assume A4,
Ellentuck, EA, global pruning, or inverse closure of the monoid.

This is a certificate for the statements and their displayed hypotheses,
not an unconditional certificate for the whole A4 theorem.

## What is now proved

`A4PairPersistence.lean` proves `persistentAcceptedPair_of_dense_pairs`.
The accepted set of second blocks is allowed to depend on the first block.
If every stem-preserving refinement contains an accepted two-block pair,
there is an accepted first block whose accepted continuations are large
below a literal realization of that block.

The proof replaces a global enumeration by finite batches at preserved
depths. At depth d, finitely many heads can end at the current cut, by A2.
If a head has no large continuation, A3 lifts an avoiding refinement below
that head to an ambient refinement preserving the whole depth-d prefix.
Process the whole finite batch, then move to the next depth. If this never
finds a persistent head, closedness gives a fusion limit. A good pair in
that limit has its first block at some exact depth d. That head was in the
batch processed at d and its second block was eliminated, a contradiction.
Occurrence and avoidance are transported by geometric reductions; there is
no assumption that every reduction factors through a chosen representative.

`A4ReviewFusion.lean` implements the final fixed-source trace fusion.
Keep the original source cut c, initial height n, and accepted set O fixed.
For each current prefix y, keep ALL exact admissible traces from c through
y, not merely the trace through the most recently chosen head. The large
set at y consists of rows h for which every composite hq belongs to O.
The already proved exact trace update identifies the accepted continuation
set after h. Pair persistence selects h while preserving largeness for the
entire updated trace family. Dependent recursion and metric fusion then
construct an infinite reduction with every selected row good after every
trace of its preceding prefix.

The finite-prefix formulation `ReviewStepGood` is deliberately used in the
limit argument: its truth depends only on a preserved finite prefix. The
proof then converts it to the ambient-row formulation required by
`oneBlock_mem_of_all_fixedTraceGoodRows`. Last-block factorization, not a
first-head factorization, covers arbitrary geometric one-step extensions.

The endpoint `review_fixedStemPigeonhole_positive` is therefore proved from
`ReviewGoodPairPrinciple`, for a positive original source cut. The not-large
case is handled by immediate avoidance; no extra partition assumption is
needed.

## Exact remaining proof boundary

`ReviewGoodPairPrinciple` is a DEFINITION of the local finite-prefix
`trace-good-pair` statement, not an axiom and not yet a proved theorem. It
asks for two geometrically compatible blocks, with the first good for the
current trace family and the second good for the entire updated family.
The global persistence/fusion argument from this local statement is no
longer missing.

The local proof uses simultaneous raw-successor-fan profiles. Raw tables
must NOT be required to be admissible. Profile saturation must hold under
all finite continuations, with original recorded occurrences retained.
The common-tail identity must be justified by actual recorded successor
codes, including coordinates where the optional profile is bottom.
`A4ReviewReplay.lean` develops this pointwise identity; its validation is
tracked separately from the 14-report fusion checkpoint above.

After common-tail correctness, the forward-saturation argument must show
that every admissible raw-fan composite is represented by a seen profile.
Only then can the Hales--Jewett colour identity imply the complete local
good-pair statement. Do not promote an identity valid only for admissible
letters to this raw-table conclusion.

The root-moving source-cut-zero case also needs the last-block coverage
argument with successors supplied by a root-moving letter. The root-fixed
case is already handled by `A4RootPigeonhole.lean`. Positivity in the current
coverage interface must not silently be dropped.

## Manuscript annotations

The finite-batch proof is a replacement for the enumeration/termination
paragraph in `lem:fixlevel` and applies to the dependent continuation family
in the review's `trace-persistence` lemma. The final A4 paragraph should keep
the original cut fixed and quantify over every exact trace of each prefix.
Add validation notes for these checked implications, but retain a partial
marker on A4 and the fat-tree Ellentuck theorem until the local good-pair
principle and the remaining root coverage are discharged.
