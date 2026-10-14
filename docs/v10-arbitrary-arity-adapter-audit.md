# Successor v10: general relational-language adapter audit

*14 October 2026. Review-only mathematical/Lean checklist. The author v10 manuscript is frozen.*

## Verified scope at the starting point

The kernel-checked `normalizedKptSMTree` works for finite Boolean
tables of unary relations, directed binary relations on distinct
vertices and singleton/diagonal information. Its M2 proof uses
actual finite **L-only** forbidden-age witnesses. It assumes that
every forbidden nontrivial structure is irreducible and the completely
neutral singleton is allowed. It makes no assumption that an arbitrary
L-age witness carries an auxiliary E-relation.

For a general finite relational signature, introduce symbols `s`
with fixed arities `arity s : Nat` and complete Boolean tables on
ordered tuples. Equality includes false atoms, repetitions and the
interpretation of nullary relations. These are the atoms formalized
in `ArbitraryArityAge.lean`.

## Important higher-arity obstruction to copying binary B3 literally

**One-upper-vertex types do not determine relations containing the new
coordinate and multiple upper vertices.**

Take a language with one ternary relation R and forbid the ordered
three-vertex structure H with R(0,1,2) true and every other tuple
false. H is irreducible: its positive tuple meets every pair.

Let the initial socle be vertices 0,1, with insertion coordinate
m=1. Let W have vertices 0,1,2,3 and precisely the positive tuple
R(1,2,3). The initial socle is completely neutral. Every complete
type of the individual upper vertex 2 or 3 over {0,1} is neutral:
the tuple R(1,2,3) is invisible in each such type because it uses
**both** upper vertices. W without vertex 1 is H-free. Nevertheless
W contains H on (1,2,3).

Consequently the naive higher-arity analogue of `CompatibleB3`
based only on each upper vertex's type over the initial socle is not
a valid age criterion. This is an obstruction to that translation,
**not** a counterexample to the manuscript's general theorem.

## Parts of the M2 proof that *do* extend atomwise

1. Ordered induced transport preserves every relation tuple, including
   negative tuples and repetitions.
2. Neutral fillers introduce no positive tuple containing a dummy.
   An irreducible nontrivial forbidden copy must lie entirely on
   genuine vertices, and a non-neutral singleton cannot lie on a
   dummy. Nullary atoms are copied unchanged.
3. A sparse pullback along increasing genuine indices and a neutral
   completion preserve forbidden avoidance.
4. Restrictions/deletions of the actual carrier preserve all atom
   tables literally; the auxiliary E structure is only added after
   constructing the source L-age model.

These are independent of the maximal arity and are the initial proof
targets of `ArbitraryArityAge.lean`.

## New obligations that must not be concealed

* **Joint mixed tuple records.** For each finite tuple of selected
  upper vertices, record all relations whose arguments can include
  several of these vertices together with initial-socle vertices,
  especially the omitted coordinate m. Single upper-vertex parameter
  types are insufficient.
* **Faithful multi-parameter image transport.** Extend the
  shape-preserving successor and canonical-prefix lemmas so the
  image of a single admissible cap determines not just its retained
  ordinary tuples but every relevant mixed tuple containing omitted
  image coordinates and more than one selected upper vertex; or
  prove such tuples are absent by the actual free-cut/no-new-tuples
  construction.
* **Generalized B3 test.** The finite age condition must reflect
  the actual admissible insertion construction and constrain these
  mixed tuples. Do not simply replace `Fin db` with an arbitrary
  symbol type in the existing binary B3 statement.
* **General finite signature representation.** Prove type finiteness,
  induced prefix closure, canonical S1--S3 successors, original and
  mapped E-column validity, M1, M3 and the reconstructed M2 for
  arbitrary relation arities. Handle diagonal repetitions
  systematically rather than treating all repeated tuples as
  unary data without an equivalence proof.
* **Nullary convention.** Either hold nullary symbols fixed across
  the ambient class or formalize separate connected components
  indexed by their interpretations. Deleting/adding a vertex does
  not change a nullary atom.

Only once these are checked should the normalized `SMTree` and
its concrete Ramsey applications be identified with the full general
language of Section 6.3. Until then the normalized result is GREEN,
the general-language adapter OPEN.

## Suggested order of formalization

Start with the arbitrary-arity atom model and induced-copy/neutral
lemmas; prove the ternary counterexample to unqualified one-upper
B3; prove complete tuple pullback and carrier restriction; then
formalize an exact mixed-tuple insertion test and the source cap's
transport properties. Audit the English proof with these tuple
zones before generalizing the M2 endpoint.
