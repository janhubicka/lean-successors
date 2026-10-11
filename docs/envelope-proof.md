# Envelope formalisation (Section 5)

This directory formalises the manuscript section **Envelopes and embedding
types** without changing the public successor-tree axioms.

## Layers

The proof is intentionally split at the mathematical boundaries used by the
manuscript.

- `Envelope.lean`: componentwise meet closure, parameter closure and the basic
  observation that the image of a shape map contains the corresponding closure.
- `EnvelopePullback.lean`: the local inverse lemma using (E1).  This is the
  only place where existence of source successor data is pulled back through a
  one-level map.
- `EnvelopeAlgorithm.lean`: finiteness of the closure and well-definedness of
  the crossing map when (I2) fails.
- `EnvelopeStage.lean`: pulls parameter closure and the crossing equations
  through the already constructed outer map.
- `EnvelopeInvariant.lean` and `EnvelopeInvariantLevels.lean`: the two
  branches of Lemma 5.8 and the exact skipped-level invariant.  The strengthened
  invariant explicitly records that stage `i` fixes every source level below
  `i`.
- `EnvelopeMinimal.lean`: two applications of shape splitting turn a gap of a
  competing envelope into a one-level map skipping the allegedly interesting
  level.
- `EnvelopePrefix.lean`: finite-prefix form of Observation 5.7.  This is
  needed because competing envelopes may be finite approximations, not only
  total maps.
- `EnvelopeMinimalityCore.lean` and `EnvelopeGlobalMinimality.lean`: every
  interesting level is forced in every competing prefix; cardinality then
  gives the height lower bound.
- `EnvelopeUniqueness.lean`: local uniqueness of inverse images for two
  admissible one-level maps realising the same crossing.  The proof is by level
  induction using (E1) and (S2).
- `EnvelopeEmbeddingType.lean`: one-step choice independence of the embedding
  type.
- `EnvelopeRun.lean`: a complete abstract run of Algorithm 5.4.  It packages
  the invariant, equality of the interesting-level sets for any two runs, and
  equality of their embedding types.
- `EnvelopeHeight.lean`: identifies the number of selected levels with the
  source height of the output and compares it with total-prefix and
  `AM^0_m` competitors.
- `EnvelopeRunExistence.lean`: finite classical recursion choosing a
  one-level factor whenever (I1)--(I3) all fail.

## Manuscript corrections exposed by the formalisation

1. Lemma 5.8 must also record that `F_i` fixes all levels below `i`; the
   proof later uses this at stage `i+1`.
2. Claim 5.9 should assert `a|_j in H_i[T]`.  The statement `a in H_i[T]`
   follows only after taking `j = ell(a)`.
3. Observation 5.7 needs its finite-prefix form for `AM` competitors.
4. In the minimality proof, the restriction before the two shape-splitting
   applications ends at the first source level `m'` crossing `i`, not at
   the competing envelope height `m`.
5. Independence of the embedding type needs a separate downward induction;
   independence of the interesting-level decisions alone does not imply it.

## Strengthening guidelines

The important reusable interfaces are:

- `OneLevelPullback`: exact formal content of (E1) used by the algorithm;
- `StageFullInvariant`: correctness invariant for a stage;
- `IsInterestingAt`: local (I1)--(I3) trichotomy;
- `AlgorithmRun`: abstract finite execution independent of how one-level
  factors are chosen.

Future weakening of the monoid axioms should try to preserve these interfaces.
In particular, the minimality proof needs a **local gap-to-one-level-factor**
operation; it does not need unrestricted duplication.  The embedding-type
proof needs local inverse uniqueness on a parameter-closed set.  Keeping these
requirements separate from the Ramsey proof will make a block/variable-word
version of the successor theorem substantially easier to compare with the
current development.
