# Section 4: transferring Ellentuck from fat trees to shape-preserving maps

**Audit checkpoint (16 October 2026).** The original construction of fat
trees is essential: the direct shape-map approximation space need **not**
satisfy Todorčević A.3(2). The already verified fat-tree space *does*
satisfy A.1–A.4 and the literal topological Ellentuck conclusion. The
unverified issue is transferring that conclusion along the canonical
projection, not repairing A.3(2) on the shape-map side.

## Verified ingredients

For an `SMTree H`, put
`R := SMTree.FatTree.approximationSystem H` and
`S := SMTree.ramseyApproximationSystem H`, and define

`π(U) := SMTree.FatTree.associatedMap H U`.

The source `FatTree.ShapeCorrespondence` proves
`associatedMap_ofShapeMap`: every `MMap H` is the projection of its
canonical fat-tree widening `ofShapeMap`. Thus **π is surjective**.
It also proves `associatedMap_level` and
`canonicalExtension_associatedMap`, identifying the image of the
first selected rows and their exact source-level cuts.

`FatTree.A4ReviewComplete` proves the unconditional
`fatTreeEllentuck` for `R` with only the original M1–M3
contract; this is **not** the claimed Ellentuck theorem on `S`.
`FatTree.A3Typed` establishes the full fat-tree A.3(2), whereas
the direct M-map space has only A.1/A.2/A.3(1) and M1 closedness.

## Adversarial decomposition of Lemma 4.1

The paper claims the canonical map `π` is continuous and open, using
the exact neighborhood image

```text
  π([x,U]_R) = [F_x, F_U]_S .
```

For this to be a valid equation, the following claims must be
**proved separately**.

1. **Projected reductions (forward factorization).** For
   `V ≤_R U`, construct a genuine right factor `G ∈ M` with
   `π(V)=π(U)∘G`. The fat-tree reduction witness stores only
   inclusions `Lift_V(i,i+1) ⊆ Lift_U(j_i,j_(i+1))`. The proved
   image containment
   `range(π(V)) ⊆ T_V ⊆ T_U` and
   `range(π(U)) ⊆ T_U` do **not** by themselves give
   `range(π(V)) ⊆ range(π(U))`, much less a right factor
   preserving all successor parameters. In particular, “forward
   inclusion is clear” in Section 4 needs an additional lemma.
2. **Finite stem compatibility.** If `V` literally begins with
   finite fat tree `x`, then the first `x.height` finite
   approximations of `π(V)` must equal the finite composition
   `F_x`, with the manuscript's precise index convention
   (finite-approximation length is last represented level + 1).
   This is an equality of **maps**, not merely terminal cuts.
3. **Relative tail lifting (reverse inclusion).** Given a
   compatible finite stem `x` of `U` and an arbitrary target
   `F=π(U)∘G` extending `F_x`, produce `V ≤_R U`
   beginning **literally** with `x` and having `π(V)=F`.
   The paper builds approximate fat refinements `U_i` and then
   says to replace their initial rows by `x`. That last
   replacement must preserve both *every* oneLift inclusion at
   the junction and the total projected map. The available fat
   A.3(2) splice does not assert either equality automatically.
4. **Finite-stem realization for arbitrary `[f,F]`.** Given
   a compatible monoid prefix `f=F∘g` at finite depth, choose
   `U` with `π(U)=F` and a finite stem `x` occurring in
   `U` such that `F_x=f` and the fat-tree occurrence depth
   agrees with `depth_F(f)`. Surjectivity of `π` supplies
   only `U`, not this *relative finite* realization.
5. **Continuity at all fibres.** The printed equality for a
   single `x,U` would imply openness on that basic set.
   Continuity additionally requires that if `π(V)∈[f,F]`,
   some fat neighborhood of the **particular** `V` has image
   contained in `[f,F]`. The printed assertion that the
   inverse image is the union of all `[x,U]` with
   `F_x=f, F_U=F` silently assumes a lifting of the
   particular fat-tree fibre. Projected reductions plus finite
   stem compatibility could provide an alternative proof
   of this continuity step.

No item above follows just from `associatedMap_ofShapeMap` or
the **forward one-row realization** in
`FatTree.ShapeRealization`; those results prove important, but
strictly weaker, facts.

## Correct topological transfer once the bridge is available

Suppose `π` is a surjective, continuous and open map satisfying
the exact relative neighborhood formula, together with the
finite-stem/depth realization in item 4. For `X ⊆ M` with the
Baire property:

- Because `π` is continuous **and open**, the preimage of a
  nowhere-dense subset of `M` is nowhere dense in `R`;
  therefore the preimage of a meagre set is meagre, and
  `π⁻¹(X)` retains the Baire property.
- Lift any nonempty monoid basic neighborhood `[f,F]` to
  `[x,U]` with `π(U)=F`, `F_x=f`, and matching depth.
  Apply the **checked fat-tree Ellentuck theorem** to the
  colouring `π⁻¹(X)` below this stem, obtaining
  `V∈[depth_U(x),U]` homogeneous on `[x,V]`.
- Use the exact image equality again:
  `π([x,V])=[f,π(V)]`. The depth-compatibility
  proof ensures `π(V) ∈ [depth_F(f),F]`.
  Therefore `[f,π(V)]` is entirely in or out of `X`.
  The Ramsey-null argument is identical using the
  nowhere-dense/meagre preimage property.

This is the **original transfer route**. It uses fat-tree A.3
rather than a fictitious A.3(2) for the monoid.

## Concrete next proof checks

1. Test **projected reductions** against the unrestricted
   geometric `ReductionWitness`, preferably first on a
   small explicit `SMTree` with nontrivial successor parameter
   lists. If false, the proposed equality requires a correction
   or a cofinal fat-neighborhood subsystem.
2. Formally prove **finite prefix stability** of `associatedMap`
   under exact equality of fat-tree rows. This is simpler than
   projecting reductions and is required by any route.
3. Prove **relative finite-stem lifting** from the original
   `Proposition 2.2` splitting lemma, not from the unrelated
   direct A.3(2).
4. Independently audit the claimed **tail splice** that
   replaces the initial rows of `V'` by a specified `x`.
   Use `FatTree.Amalgamation.splice` to enforce the oneLift
   reduction at the junction; do not infer it from agreement of
   the total map alone.
5. After the exact neighborhood identity is checked, put the
   **topological transfer** in a theorem with the manuscript's
   original `[f,F]` Ramsey/Ramsey-null definitions. Do not
   substitute finite-dimensional Ramsey or fat-tree Ellentuck
   for the missing final transfer.

**Source correction already identified:** in the printed
Ramsey-null paragraph, the avoided neighborhood is
`[f,F_V]`, not `[n,F_V]`. The monoid approximation length
is last source level + 1, unlike the printed last-level depth
convention.

## Maintenance decision

PR #559, which pursued *direct M-space A.4*, was closed
without merge after clarification that the direct space does
not have A.3(2). The code remains in Git history, but it is
not needed for the original Ellentuck proof route. The checked
closedness theorem merged in #558 can remain a reusable
fact and does not add an axiom or alter M1–M3.

The mathematics above is an **adversarial proof inventory**,
not a claim that the transfer has been validated.
