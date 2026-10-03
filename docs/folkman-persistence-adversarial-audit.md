# Adversarial audit: Folkman--BANANA persistent colouring and copy degree

Scope: `SuccessorTree/NonPrecompact/FolkmanPersistence.lean`.

The target is the full circulation theorem `thm:folkman-infinite-degree`,
not merely the subset-sum witness in `ColouringWrappers.lean`.

## Referee A: finite atom presentation and non-unital embeddings

A finite Boolean ring is the ring of subsets of its finite atom set.  A
Boolean-ring embedding need not preserve the greatest element.  On atoms it
therefore assigns to every source atom a nonempty block of target atoms,
with distinct source atoms receiving disjoint blocks; target atoms outside
all these blocks are unused.

`FolkmanAtomEmbedding` encodes exactly this by an `Option`-valued owner
map on each sort.  A target atom with owner `some i` lies in the block of
source atom `i`, while owner `none` means that it lies outside the image.
The owner function makes distinct fibres disjoint automatically, and the
nonempty-fibre fields express injectivity of the Boolean-ring embedding.

The bilinear map is determined by source atom pairs.  The
`pairing_parity` field states that the parity of the ordinary number of
ambient incident atom pairs between two owner fibres equals the source
atom-pair value.  By additivity, this is equivalent to preservation of the
bilinear map on arbitrary unions of source-atom fibres.

Thus the formal atom presentation is equivalent to the circulation
definition of finite Folkman--BANANA structures and embeddings.

## Referee B: source copies and the ordinary count

A copy of `A_×` consists of one nonzero element on each sort whose pairing
is one.  In atom coordinates these elements are nonempty finite atom blocks
`X,Y`.  The manuscript count
[
 N_C(X,Y)=|{(u,v)in X	imes Y:eta_C(u,v)=1}|
]
is represented by `folkmanEdgeCount`.  Its parity is exactly the bilinear
pairing of the two elements.  Hence `FolkmanAxCopy`, which requires both
blocks nonempty and the count odd, is precisely a copy-range of `A_×`.

For a target embedding `f : B → C`, `P.Inside f` requires both source
blocks of `P` to be unions of owner fibres of `f`.  These are exactly the
left and right elements in the range of the embedded Boolean rings.
Unused `none` atoms cannot accidentally enter such a copy.

## Referee C: additivity of the ordinary count

The formal count is a double finite sum of the indicator of an incident
atom pair.  Owner fibres are pairwise disjoint, so finite-sum additivity
gives
[
 N_Cigl(igcup_{iin S}X_i,Yigr)
 =sum_{iin S}N_C(X_i,Y)
]
and the analogous identity on the right.  These are the two
`folkmanEdgeCount_biUnion_*` lemmas.

This directly justifies the manuscript's integer, not merely mod-two,
additivity assertion.  No cancellation argument in `F₂` is being used for
the ordinary count.

## Referee D: odd weights inside a diagonal target

For an embedded diagonal target `B_q^{FU}`, let `X_i,Y_j` be the owner
fibres and let `Y` be the union of all right fibres.  Pairing preservation
gives
[
 N_C(X_i,Y_j)equivdelta_{ij}pmod2 .
]
By the right-fibre additivity lemma,
[
 N_C(X_i,Y)=sum_j N_C(X_i,Y_j),
]
so its parity is one.  This is
`FolkmanAtomEmbedding.diagonal_left_to_allRight_odd`.

The argument does not require the union of target fibres to exhaust the
ambient atoms.  In particular, atoms with owner `none` play no role, as
required for non-unital embeddings.

## Referee E: one ambient colouring fixed before the target

For arbitrary ambient `C` and exponent `k`,
`exists_folkmanPersistentColouring` first fixes the colouring of every
`A_×` copy by its ordinary count modulo `2^(k+1)`, enumerating the odd
residues by `Fin (2^k)`.

Only afterwards does it quantify over an arbitrary embedding of the
diagonal target with `2^(k+1)` atoms on each side.

Remove one arbitrary left target atom (the implementation uses index zero).
The remaining `2^(k+1)-1` integers
`a_i=N_C(X_i,Y)` are all odd.  The already verified
`folkman_odd_residue_copy_witness` selects a nonempty subset whose sum has
any prescribed odd residue.  The selected left element is the union of the
corresponding left owner fibres; the right element is `Y`.

Nonemptiness follows from nonempty owner fibres, the ordinary incident count
is the selected odd sum, and both blocks are explicitly recorded as unions
of target fibres.  Thus the resulting `A_×` copy lies inside the chosen
target copy and has the prescribed ambient colour.

The colouring is never allowed to depend on the target embedding.

## Referee F: copy Ramsey degree quantifiers

`folkmanAxCopyRamseyDegreeLE t` has the standard circulation order:

1. for every finite target structure `B`;
2. for every positive finite colour set;
3. there is an ambient `C`;
4. for every colouring of `A_×` copies in `C`;
5. some embedding `B→C` sees at most `t` colours on source copies
   contained in its range.

To refute degree `t`, use the diagonal target with `2^(t+1)` atoms and
the fixed `2^t`-colour persistent colouring.  Every one of the `2^t`
colours occurs inside the target embedding supplied by the putative degree
witness, contradicting `t<2^t`.  The case `t=0` is included.

## Boundary cases and clarity

The persistent target always has at least two atoms per sort, so choosing
the omitted index and the all-right union is legitimate.  The selected
subset returned by the Folkman wrapper is nonempty, so the selected left
element is nonzero.  The all-right element is nonzero because every target
right atom has a nonempty owner fibre.

The circulation proof is mathematically aligned with the formal proof.
The formalisation makes explicit the one point that is easy to blur in
prose: a non-unital target embedding may leave ambient atoms unused, and
the constructed source copy uses only unions of target fibres, never those
unused atoms.

No mathematical correction to `thm:folkman-infinite-degree` was found.
