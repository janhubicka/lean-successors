# Binary type-respecting Ramsey theorem

Use the narrow public import:

```lean
import SuccessorTree.Library.TypeRespecting

open SuccessorTree.V10

#check @normalizedKpt_typeRespectingRamsey
#check @FiniteTypeProfileMap.extends
#check @TypeRespectingEmbedding.restrictionEquiv
```

The dependency uses the repository's pinned Lean toolchain and Mathlib revision.
In another Lake project, require `successor-tree-lean` from
`https://github.com/janhubicka/lean-successors.git` at the chosen checked commit,
then import `SuccessorTree.Library.TypeRespecting`.

## Statement and objects

For a finite admissible partial structure `A` and any finite colouring of
`TypeRespectingEmbedding A`, `normalizedKpt_typeRespectingRamsey` returns
`F : SMTree.MMap (normalizedKptSMTree family)` such that

```lean
∀ f g : TypeRespectingEmbedding A,
  colour (TypeRespectingEmbedding.act A F f) =
    colour (TypeRespectingEmbedding.act A F g)
```

The action is literal postcomposition on the finite functions:

```lean
(TypeRespectingEmbedding.act A F f).1 u = F (f.1 u)
```

`FiniteTypeBase family` contains an enumerated finite partial structure and its
forbidden-family avoidance proof. Its auxiliary E relation satisfies the
repository's partial-structure and free-level axioms. `TypeProfile A` contains **every** admissible
full partial type over every initial ordinary socle of `A`, including its top
front. It does not contain only the types realized by vertices of `A`.

`CoherentTypeProfileMap A B` has an injective function on this full profile, a strictly increasing
cut map fixing zero and taking the top cut to the top cut, full ordinary-socle
compatibility, fixed roots, prefix coherence and the weak canonical successor law.
For every source successor equation whose base, parameters and successor lie in
the profile, applying the map preserves the letter and gives a **defined**
successor below the prescribed image of the source successor. Thus this law also
controls the existence of the target canonical step.

`FiniteTypeProfileMap A B` also preserves permitted finite labelled
L-continuations. Upper carriers may be any finite ordered subset of a bounded
interval; labels may repeat; the upper carrier may be empty. The auxiliary E
relation belongs to full partial types and bases, and is not imposed on an
L-continuation. At a cut `i`, the continuation condition forces each used label
to have level `i`; unused slots impose no condition. The `age` field supplies an
allowed target continuation with the transported labels and the same induced
upper L-structure. For any supplied source and target continuations with this
same upper structure, `FiniteTypeProfileMap.age_iff` proves equivalence of their
forbidden-family avoidance.

`TypeRespectingEmbedding A` identifies these intrinsic maps by their actual
finite functions. A finite target base and its finite certificate are
existentially quantified. **Global extendibility is not in the definition.**

## Using a finite certificate

An intrinsic map into a specified finite base gives one of the coloured objects
directly:

```lean
example {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {A B : FiniteTypeBase family} (h : FiniteTypeProfileMap A B) :
    TypeRespectingEmbedding A :=
  ⟨h.toCoherentTypeProfileMap.toFun, B, h, rfl⟩
```

For the underlying ordered vertex embedding, use
`h.toCoherentTypeProfileMap.vertexMap : Fin A.size → Fin B.size`.
Its strict monotonicity and complete atom equalities are separate interfaces
listed below. `TypeRespectingEmbedding.exists_extension` supplies an extension
of an already packaged coloured object as a normalized monoid map.

Conversely, `FiniteTypeProfileMap.ofShapeMap A F hF` constructs the finite
certificate of any global normalized map. Its target is `A.shapeImage F`, the
**entire** ordinary socle of the image of a cap at level `A.size`. Its size is the
image of that terminal cut, including every inserted target coordinate.

## Checked proof interfaces

| Mathematical step | Interface |
| --- | --- |
| Every profile front is inhabited | `TypeProfile.front_nonempty` |
| Recover every retained full L+ atom | `CoherentTypeProfileMap.recovers_complete_record` |
| Strictly increasing ordinary vertex map | `CoherentTypeProfileMap.vertexMap_strictMono` |
| All induced L+ atom equalities | `CoherentTypeProfileMap.vertexMap_preserves_atoms` |
| Exact free-cut transport | `CoherentTypeProfileMap.vertexMap_freeLevel` |
| Exact actual partial-type transport | `CoherentTypeProfileMap.vertexType_transport` |
| Full L+ type-respecting implication | `CoherentTypeProfileMap.preserves_full_type_equality` |
| Intrinsic age gives the boring-extension test | `FiniteTypeProfileMap.compatibleB3_of_front_prefixes` |
| Insert one prescribed target coordinate | `FiniteTypeProfileMap.extend_front_once` |
| Extend the entire intrinsic finite map | `FiniteTypeProfileMap.extends` |
| Restrict any normalized global map intrinsically | `FiniteTypeProfileMap.ofShapeMap` |
| Identify intrinsic maps with monoid restrictions | `TypeRespectingEmbedding.restrictionEquiv` |
| Literal postcomposition on profile values | `TypeRespectingEmbedding.act_apply` |
| Reusable bounded-restriction Ramsey argument | `SuccessorTree.SMTree.boundedRestrictionRamsey` |
| Binary intrinsic Ramsey corollary | `normalizedKpt_typeRespectingRamsey` |

The finite extension is proved by source-front induction. Canonical gap closing
initializes the next front, and the already established compatible boring
extension inserts each remaining target coordinate. The Ramsey proof uses the
existing finite-dimensional shape theorem on source levels below `A.size + 1`.

## Scope and verification

The presentation is the normalized finite unary/directed-binary/diagonal
language. A forbidden family is a finite list of `NormalizedForbidden` patterns:
each is either a non-neutral singleton or an irreducible pattern of size at
least two. The chosen neutral singleton is allowed, and the empty forbidden
pattern is excluded. Avoidance means absence of an **ordered induced** copy.
The auxiliary E relation is retained. In particular the
full L+ type-respecting implication includes E; dropping E is not an exported
consequence. Empty bases, empty forbidden families and repeated upper labels
are included by the quantified statements.

More precisely, `preserves_full_type_equality` applies to vertices `v, w` of `A`
and a cut `i ≤ v.val, w.val`. Equality of their complete `A.str.partialTypeAt i`
records implies equality of the complete target records over the entire cut
`h.levelMap i`, including the newly inserted target vertices. This auxiliary
conclusion already follows from the coherent part of the finite certificate.

Run the complete narrow export and exact named axiom check with:

```sh
lake build SuccessorTree.Library.TypeRespecting
lake env lean scripts/CheckV10TypeRespecting.lean > type-respecting-axioms.log
python3 scripts/check-axiom-log.py type-respecting-axioms.log scripts/CheckV10TypeRespecting.lean
```

The checker also elaborates an example using only the public import. The named
axiom parser accepts only `propext`, `Classical.choice` and `Quot.sound` and
rejects omitted, extra or substituted declarations. The generic Ramsey lemma
is also in `scripts/CheckPublicTheoryAxioms.lean`; the binary endpoints have the
single dynamic V10 CI owner.
