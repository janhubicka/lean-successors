# Adversarial audit: pre-BANANA persistent colouring and copy degree

Scope:
- `SuccessorTree/NonPrecompact/PrebananaPersistence.lean`
- `SuccessorTree/NonPrecompact/PrebananaCopyDegree.lean`

The aim is to check the exact circulation statement for
`thm:pre-banana-colouring`, not merely the subset-sum lemma underneath it.

## Referee A: atom-coordinate presentation

A finite Boolean algebra is completely determined by its finite set of
atoms.  In the standard presentation with atom set `Fin n`, a unital
Boolean-algebra embedding from a source with atom set `Fin q` into a
target with atom set `Fin n` is exactly a function
`part : Fin n → Fin q` whose fibres are nonempty: the fibre of a source
atom is the set of target atoms below its image.  Every target atom lies in
exactly one fibre because the embedding is unital.

The additional pre-BANANA marking is preserved precisely when, for every
source atom, the parity of the number of marked target atoms in its fibre is
the source mark.  This is the definition of `PrebananaAtomEmbedding`.
Thus the atom-coordinate presentation is equivalent to the manuscript's
finite structures and embeddings; no extra ordering of atoms is part of the
structure.

## Referee B: copies of the two-marked-atom source

An unordered copy of the two-atom source is a partition of the ambient atom
set into two blocks, each with odd marked-atom count.  The formal type
`PrebananaTwoAtomCopy mark cstar` records only the unique block containing
one fixed ambient atom `cstar`.  Its complement is the other block.

This is a canonical encoding of copy-ranges, not of ordered embeddings:
swapping the two source atoms does not change the encoded copy because the
block containing `cstar` is unchanged.  Odd marked count implies each block
is nonempty, so no separate nonemptiness field is required.

The choice of `cstar` belongs only to the ambient colouring.  It is not
named in the structure and is not required to be respected by target
embeddings, exactly as in the circulation proof.

## Referee C: one colouring fixed before the target

For an arbitrary ambient marking `mark : Fin n → F₂`, the theorem
`exists_prebananaPersistentColouring` fixes `cstar=0` and colours every
two-atom copy by the marked count of its canonical block modulo
`2^(k+1)`, enumerating the odd residues by `Fin (2^k)`.

Only after this colouring is fixed does the theorem quantify over an
arbitrary embedded all-marked target with `2^(k+1)` atoms.  The target is
represented by an arbitrary partition function `part` whose every fibre
has odd marked count.  No aspect of the colouring depends on this partition.

Let `jstar=part(cstar)`.  Removing `jstar` leaves exactly
`2^(k+1)-1` target fibres.  Applying
`prebanana_odd_residue_copy_witness` to their odd marked counts and to the
odd count of the distinguished fibre selects a union that realises any
prescribed odd residue.  The selected block contains `cstar`; the wrapper
also proves that both it and its complement have odd marked count.

The formal proof records the selected block as a union of target fibres.
Therefore the resulting source copy lies inside the chosen target copy, not
merely somewhere in the ambient structure.

## Referee D: copy Ramsey degree quantifiers

`prebananaTwoMarkedCopyRamseyDegreeLE t` follows the manuscript order:

1. for every finite target structure `B`;
2. for every positive number of colours `r`;
3. there exists an ambient structure `C`;
4. for every colouring of source copies in `C`;
5. there is an embedding `B → C`;
6. on whose source copies at most `t` colours occur.

The predicate `Inside` says the selected source block is a union of target
fibres.  Since the embedding is unital, the complement is automatically the
union of the complementary target fibres, so this is exactly containment of
the unordered two-block copy in the target range.

To contradict degree `t`, choose the all-marked target with
`2^(t+1)` atoms and the `2^t`-colour persistent colouring supplied after
the degree hypothesis chooses its ambient `C`.  Persistence forces every
one of the `2^t` colours inside the target embedding, whereas the degree
hypothesis allows at most `t`.  The elementary inequality
`t < 2^t` gives the contradiction, including `t=0`.

## Referee E: parity and boundary cases

The all-marked target is a legal pre-BANANA structure because
`2^(k+1)` is even, so the total mark is zero modulo two.  This remains true
for `k=0`, where the target has two atoms and the palette has one colour.

The persistent theorem itself is slightly stronger than needed: it accepts
an arbitrary ambient marking and does not assume its total parity is even.
The copy-degree theorem applies it only to ambient structures satisfying the
pre-BANANA class axiom, so this strengthening is harmless.

No assumption that the distinguished ambient atom is marked is needed.  It
lies in some target fibre, and that fibre has odd marked count because the
target is all-marked and the embedding preserves marking.

## Clarity audit

The circulation proof already explains the role of `c_*` correctly.  The
formalisation confirms two points worth keeping explicit:
- the colouring is fixed before the target copy is chosen;
- the resulting block is a union of target fibres, so the source copy really
  lies inside that target copy.

No mathematical correction to `thm:pre-banana-colouring` was found.
