# Successor v10: M2 finite-age bridge (14 October 2026)

This is a **proof roadmap**, not a claim that M2 is already proved. The
checked inputs are in the modules named below. The decisive remaining Lean
task is the explicit boundary-label extraction described in Step 2.

## Setup

Let (F\in K_{pt}M), let (n>0) be the first source level after a
nontrivial image gap, let \(\lambda\) be its strictly increasing level
function, and put \(m=\lambda(n)-1\). Thus
\(\lambda(i)<m\) for every \(i<n\), and \(\lambda(n)=m+1\).
Write \(D\) for the genuine intrinsic deletion ShapeMap, so at
source level \(n\) its image is the complete predecessor of \(F(x)\).

The desired boundary prescription is
\[
    D(x) \longmapsto F(x) \quad (\operatorname{lev}(x)=n).
\]
The exact source-level B1 identity is
`uniformGapDeletedShapeMap_boundary_raw_ancestor`; B2 is supplied by
`shapeMap_transfers_ordinary_compatibility`.
`uniformGapDeletedShapeMap_factorization_of_compatibleB3` gives the
one-gap factorization once this is packaged into
`PrescribedBoringData` with `CompatibleB3`.

## Step 1: a putative finite L-age obstruction

Fix one original boundary source (x_0), and let (W) be a finite
ordered **L-structure** matching the full initial socle of (F(x_0))
through coordinate (m). Suppose each upper vertex of (W) has its
complete L-type through (m) equal to the L-reduct of a prescribed
(F(x_i)), with (D(x_i)) ordinary-compatible with (D(x_0)).
Assume (W\setminus\{m\}) is forbidden-free, but some normalized
forbidden pattern has an induced ordered realization (e) in (W).

No auxiliary E-relation is assumed on (W). In particular, this is
the repaired finite age-test, not the older, effectively vacuous
condition on consecutive vertices of an E-partial structure.

## Step 2 (OPEN): extract the genuine level-n source labels

For each upper vertex appearing in (e), choose one corresponding
boundary node (x_i), put (T_i=x_i.1.2), and use the explicit
boundary prescription to prove, with all dependent casts accounted for:

1. Each (T_i) is genuinely admissible at source level (n).
2. (T_i) and (T_0) have the **same ordinary L+ socle** by
   reflection of compatibility through (D).
3. The actual complete prefix record of (W) at (e(i)), through
   (m+1=\lambda(n)), equals (F(x_i).1.2.\mathrm{lReduct}).
4. The retained low/low L records in (W) at all
   \(\lambda(k)\), \(k<n\), equal the corresponding records of (T_0).
5. Coordinates \(0,\dots,m\) occur in the carrier of (W),
   and deleting (m) avoids all forbidden patterns.

The numerical target coordinate (m), although **omitted by**
\(\lambda\), is included in these complete image parameter types.
Do not replace complete ordinary types by restricted retained
coordinate records: that loses precisely the data required by B3.

## Step 3: contradiction after the labels are extracted

If the realization (e) has no upper vertex, it lies entirely in
the common initial socle and hence occurs already in the admissible
(F(x_0)). This is excluded by
`sameInitialL_realizes_below` and
`forbiddenCopy_has_upper_of_sameInitialL`
(`M2B3CopyCases.lean`, PR #371).

Otherwise choose at least one upper index. Apply
`boundedCopySourceAge_selected_family_padded_with_L` to the actual
source labels (T_i), the target (W\setminus\{m\}), the retained
low levels \(\lambda(0),\dots,\lambda(n-1)\), and precisely the
upper vertices in (e). The sparse carrier pullback and neutral
filler preserve **all** selected upper--upper L atoms and negative
facts, rather than freely completing them. Construct the auxiliary
E-relation only on the padded **source**. This produces one genuine
admissible finite (B) containing all selected types with the exact
pulled-back L-reduct.

Cap (B) by the verified neutral socle-cap construction. For every
selected upper type, the canonical parameter-prefix theorem transports
the **entire** target type through (F), including target coordinate
(m). One upper type itself identifies the common initial L socle:
`sameInitialL_of_complete_upper_type`. Full retained-record recovery
determines the upper--upper atoms. Hence the mapped cap realizes the
entire forbidden pattern as an induced ordered copy, contradicting
its admissibility.

The combination *after* these Step 2 input facts is
`m2B3_selected_upper_forbidden_contradiction`
(`M2B3SelectedContradiction.lean`, PR #372). Check its exact-head
Lean build and transitive axiom audit before marking this component
validated.

## Step 4 (OPEN): the boundary prescription and M2 endpoint

Package all boundary inputs (D(x)) and outputs (F(x)) into a
single `PrescribedBoringData`. Prove source injectivity, target
admissibility, B1, B2, and the literal boundary equality.
Use Steps 1--3 to verify its `CompatibleB3` finite **L-age** test,
then invoke `uniformGapDeletedShapeMap_factorization_of_compatibleB3`.
This yields the exact two-map factorization through the first
affected source level.

### Review checkpoints

- **Do not** infer the corrected B3 from the printed B3 over initially
  enumerated E-partial structures: spacing already forbids the first
  consecutive upper E-edge.
- **Do not** assume that W admits an E-expansion, or that `F` preserves
  arbitrary L-age. Only selected complete types from actual admissible
  source nodes may be transported.
- Check every missing L relation, both binary orientations, loops,
  unary and diagonal predicates; induced copying requires equalities,
  not merely preservation of positive edges.
- The first intrinsic deletion factor, its B1 predecessor record and
  B2 compatibility transport are established separately. The proof of
  Step 4 must not import the M2 axiom itself.
