# V10 manuscript review — Theorem 1.11, 16 October 2026

**Author-facing TODO only.** No changes are made to the frozen
mathematical prose or to the four previously approved repairs.

## Proposed mathematical correction

The original Theorem 1.11 (all Ellentuck-Baire subsets of the
shape-preserving monoid are Ramsey, all Ellentuck-meagre subsets
Ramsey null) appears **false under M1–M3**.

An explicit ZFC English proof is in
[`docs/theorem111-zfc-counterexample-20261016.md`](../docs/theorem111-zfc-counterexample-20261016.md),
with a separate
[adversarial audit](../docs/theorem111-zfc-counterexample-referee-20261016.md).
The counterexample is the already-verified free-ancestral
one-letter, one-ancestral-parameter S-tree with its full shape
monoid. It constructs a **closed nowhere-dense** subset Z of the
**monoid Ellentuck topology** meeting every pure refinement
of one nonempty basic neighbourhood [f,Id].
Consequently Z is not Ramsey null; its dense open complement
is not Ramsey.

This is independent of the earlier failure of the Section 4
projection Lemma 4.1. The latter only defeats a proof,
whereas the new construction defeats the claimed theorem
**itself** if the English argument survives author review.

## Exact editorial suggestions — do not apply automatically

1. Reclassify Theorem 1.11 as a conjectural/invalid statement
   until a correct qualified version is found. Avoid marking
   the existing Section 4 proof as Lean validated.
2. Keep Theorem 1.17, the Ellentuck theorem for **fat trees**:
   it is already verified in Lean with genuine fat A.3 and A.4.
3. Keep Theorem 1.6, the finite shape-preserving Ramsey theorem:
   its Lean proof does not use Theorem 1.11.
4. Revise the paragraph and any introduction claims saying
   that the monoid M itself is a topological Ramsey space.
   Distinguish it from the fat-tree Ramsey space and the
   simpler pointwise-Borel **fat-image** result.
5. Remove or qualify the identity
   `π[[x,U]]=[F_x,F_U]` from Lemma 4.1:
   the earlier one-parameter free-ancestral witness already
   obstructs it, and the delayed witnesses obstruct continuity.
6. Recheck any other manuscripts or downstream proofs citing
   Theorem 1.11 specifically. The theorem about finite
   shape copies and the big-Ramsey application are independently
   proved and should not lose validation marks.
7. If the authors want a replacement, a precise sound
   English statement is the pointwise-Borel fat-image theorem
   in `docs/section4-fat-tree-relative-transfer-english-20261016.md`,
   not the original all-Ellentuck-Baire claim.

## Verification boundary

The English proof is complete and has passed an independent-criteria
adversarial mathematical review, with deterministic finite-history
and pure-map compatibility regressions.

**No Lean proof of the infinite marked maps (Q_A), their
compatibility lemma, or the transfinite recursion has yet been
completed.** Before publishing an erratum, have a human referee
independently check the explicit root-parameter marker on all
skipped levels and the nowhere-density argument.

No source-proof edits or authorial editorial decisions were made
on this PR. The manuscript remains frozen.
