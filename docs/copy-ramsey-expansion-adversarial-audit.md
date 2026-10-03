# Adversarial audit: abstract copy Ramsey expansion bound

Scope: `SuccessorTree/CopyRamsey.lean`.

The target is the circulation lemma `lem:expansion-degree-bound`:
if a source has finitely many expansion types in a precompact Ramsey
expansion, then its reduct copy Ramsey degree is at most that number.

## Referee A: abstract copy interface

`FiniteCopySystem` separates embeddings from copy-ranges.  The map
`range : Emb A B → Copy A B` is required to be surjective, not injective.
Thus automorphisms of the source, and more generally distinct embeddings
with the same range, are allowed.

An embedding `g : B → C` transports an `A`-copy in `B` to an
`A`-copy in `C`.  The axiom
`range(comp f g) = mapCopy g (range f)` is exactly the compatibility
needed to compare embedding Ramsey statements upstairs with copy colourings
downstairs.

The definition `CopyRamseyDegreeLE` has the manuscript quantifier order:
for every target `B` and every positive number of colours `r`, there is
an ambient `C` such that every colouring of `A`-copies in `C` has a
`B`-copy seeing at most the stated number of colours.

## Referee B: expansion interface

`RamseyExpansion` records a finite set of expansion types for each reduct
object and a hereditary restriction operation along reduct embeddings.
The identities
[
 (C^*|g)|f=C^*|(gcirc f),qquad A^*|mathrm{id}=A^*
]
are explicit axioms.

The Ramsey axiom is the embedding Ramsey property for specified expansion
types.  It colours expanded embeddings and produces an expanded target
embedding on which all expanded source embeddings have one colour.

The proof of the degree bound needs only:
- finiteness of the source expansion types;
- existence of at least one expansion of the reduct target;
- heredity/restriction;
- the expanded Ramsey property.

It does not use a lifting/reasonability axiom separately.  In the manuscript
a “Ramsey expansion” is reasonable by definition, so the formal assumptions
are weaker than the stated hypotheses, not stronger.

## Referee C: simultaneous homogenisation

`simultaneous_ramsey` proves the finite iteration used in the prose.

For the empty set of source expansion types the target expansion itself
works.  At an insertion step, first take a Ramsey witness for the new type
over the target supplied by the induction hypothesis.  Pull all remaining
colourings back through that witness, apply the induction hypothesis, and
compose the two target embeddings.

For the newly inserted type, homogeneity follows from the last Ramsey step
applied to the two composites into the intermediate target.  For all earlier
types it follows from the induction hypothesis applied to the pulled-back
colourings.  Associativity of reduct embedding composition is the only
coherence used here.

This is precisely the “working backwards through the Ramsey witnesses”
argument in the circulation proof.

## Referee D: reduction from copy colours to expansion types

Fix a reduct target `B`, an expansion `b` of it, and a reduct copy
colouring in the final ambient `C`.

For each expansion type `a` of `A`, colour an expanded embedding
`e : a → c` by the colour of its reduct range.  Simultaneous Ramsey gives
an expanded embedding `g : b → c` on which this colour is constant for
each fixed source expansion type.

Now take a reduct copy `p` of `A` in `B`.  Surjectivity of `range`
chooses one embedding representative `rep(p)`; restricting `b` along it
assigns an expansion type `type(p)`.

This choice need not be canonical and need not be invariant under
automorphisms of `A`.  That is harmless.  If two chosen representatives
produce the same expansion type, simultaneous homogeneity says their
transported reduct copies under `g` have the same colour.  Therefore the
colour on copies inside the selected `B`-copy factors through the finite
set of expansion types.

The finite image of a function factoring through a set of size `t` has
size at most `t`.  The formal proof implements this by defining one colour
per expansion type (arbitrarily on types not represented in `B`) and using
finite-set image inclusion.

## Referee E: non-rigidity

No step identifies copies with embeddings.  The only use of an embedding
representative of a copy is through the surjective range map, and all final
colour sets are sets of reduct copies.

Consequently the proof verifies the manuscript sentence that the
expansion-degree bound does not require rigidity of the reduct source.

## Boundary cases

If an expansion type of `A` has no embedding into the chosen target
expansion `b`, its homogeneity condition is vacuous.  It can still be
counted among the finitely many expansion types, which only weakens the
upper bound.

The number of colours is required to be positive, matching the circulation
definition.  This also provides a default colour for expansion types not
represented inside `B`.

Since every reduct object has at least one expansion type in the interface,
the source type set is nonempty; nevertheless the simultaneous Ramsey lemma
is proved for an arbitrary finite subset, including the empty one.

## Clarity audit

The circulation proof is correct and accurately describes the backwards
finite iteration.  The formalisation suggests one small conceptual
clarification: reasonability is part of the paper's definition of “Ramsey
expansion”, but the proof of this particular lemma uses only heredity,
existence/finiteness of expansion types, and the expanded Ramsey property.

No mathematical correction to `lem:expansion-degree-bound` was found.
