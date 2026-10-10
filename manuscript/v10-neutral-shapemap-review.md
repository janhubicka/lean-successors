# Successor v10: neutral one-gap Kpt map and its precise scope

Reviewed proof chain: draft PRs 168--183, stacked in order.
PRs 168--183 now have passing focused Lean builds and transitive
axiom audits. In particular the exact-head PR 183 checkpoint
\`25668dab4644e885b84a7ec3cccdc5e6cfa18f3d\` passed focused
V10 run \`38075729225\`. The full repository rerun is recorded
separately in CI; the focused proof endpoints use only standard
Lean axioms.

## What the neutral branch proves

- Exact old L+ record transport through one-coordinate insertion,
  including both orientations, negative directed tuples, unary,
  diagonal, loops and auxiliary E
- Exact E row/column of the newly inserted coordinate, with its
  cross E-row given by the old row at ell-1
- Full-record equality across different ambient representatives,
  and a unique admissible image at the transported E free level
- Order preservation on all actual Kpt prefixes, including those
  crossing the skipped level
- Injectivity on admissible Kpt nodes
- A terminal Sigma-letter transport theorem and exact transport of
  the EMPTY or singleton canonical successor parameter list
- The boundary weak-successor theorem: for a step based at ell-1,
  the OLD successor is a prefix of the mapped output, even though
  the new coordinate inserts an extra step
- A separately staged above-gap exact successor theorem, complete
  ShapeMap and level-range theorem

## Remaining obligations, not inferable from neutral insertion

The manuscript's Lemma 6.51 is about an arbitrary prescribed
crossing f on the matching socle. Its map may insert NON-neutral L
atoms at ell. The neutral map is the fallback used for mismatching
socles, not a replacement for that prescribed branch.

The finite common-socle age test has already been proved as a
conditional finite-structure theorem: forbidden copies outside the
inserted coordinate pull back; those containing it reduce to a
finite L-witness with prescribed upper crossings. Still required:
uniformity on all Kpt types, derivation of the exact crossing from
f, image admissibility in every matching-socle case, compatibility
with the canonical successor operation, and assembly into a
shape-preserving one-level map.

Even a proof that a neutral map skips only ell would not give M2,
M3 or the published big-Ramsey upper-bound application; those
require the non-neutral prescribed maps and the remaining
decomposition/duplication arguments.

### Possible editorial insertion

At Lemma 6.51 explain that the inserted neutral vertex is L-isolated
only in the mismatching-socle case, NOT L+-isolated: it can have
prescribed auxiliary E relations to shifted later type vertices.
For finite L-age witnesses whose carrier is an arbitrary bounded
subset of Nat, either clarify that finite enumerated structures
allow this or add a short order-compression lemma fixing the
initial ell+1 socle. The mathematical source is unchanged here.

The existing four author repairs and all unmarked manuscript prose
are preserved; current author-edited main.tex was not available
as verified raw bytes for this checkpoint. No independent referee
agents were invoked.

## Exact one-gap range theorem (PR 183)

The all-neutral finite partial structure on n+2 vertices has no
non-neutral singleton or irreducible binary configuration, and its
only E column consists of (u,n+1) for u<n. Hence the last vertex
has canonical free level n. Every level n of the actual normalized
Kpt tree is therefore nonempty, without assuming M3.
The neutral ShapeMap consequently satisfies SkipsOnly ell for
every positive ell. This is strictly stronger than simply omitting
ell from its level range.

This does not realize arbitrary prescribed non-neutral f crossings.
The application of the three-clause age test to a globally selected
insertion map, M2/M3 and the final big-Ramsey bound are still open.
