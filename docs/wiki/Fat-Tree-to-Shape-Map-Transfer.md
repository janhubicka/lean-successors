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

## Explicit free-ancestral obstruction to the forward inclusion

**Important adversarial finding (mathematically explicit; Lean instance
proof still pending).** The geometric-to-algebraic implication in item 1
appears to be **false for the unrestricted fat-tree reduction**. A
small witness exists in the already verified `FreeAncestral.freeSMTree`
with one ancestral parameter and one label; its monoid is the full
set of shape maps. Denote histories by their successive parameter
lists. The empty list `[]` is a successor code without a parameter,
and `[j]` is the single ancestral parameter at level `j`.

Let `E₀` insert an empty code at target level 0, and let `E₂`
insert code `[0]` at level 2. Both are existing
`FreeAncestral.oneGapShapeMap` instances, and hence elements of the
full monoid. Construct the infinite fat trees

```text
  U.cut = (0, 2, 3, 4, 5, ...)
  U.rows = (E₀, id, id, id, ...)

  V.cut = (0, 2, 4, 5, 6, ...)
  V.rows = (E₀, E₂, id, id, ...).
```

Here `rows` denotes the finite one-row approximations induced by
the displayed maps at each prescribed source cut, with their
canonical extensions; in particular, `E₀` is canonical at
source cut 0 and `E₂` at source cut 2. The natural index map
witnessing `V ≤_fat U` is

```text
  φ(0)=0, φ(1)=1, φ(i)=i+1 for every i≥2.
```

It matches the cuts at **all** indices. At row 0 the two one-lifts
are equal. At row 1, the ambient U rows are identities: its lift
from cut 2 to cut 4 contains **every** level-4 successor history
above a level-2 history, so it contains the V one-lift regardless
of the E₂ insertion. At every row `i≥2`, both sides are the
same identity one-lift across consecutive cuts. Therefore the
geometric reduction witness satisfies all the required one-lift
inclusions, not merely a bounded-depth test.

But the associated shape maps are

```text
  π(U) = E₀,       π(V) = E₂ ∘ E₀.
```

Let `a` be the unique source history at level 1: `a = ([]) `.
Then

```text
  E₀(a)       = ([], [])
  E₂(E₀(a))   = ([], [], [0]).
```

Every `E₀` image at level 3 comes from a level-2 source
history. The only possibilities (one label, one ancestral
parameter) are

```text
  ([], [], [])    or    ([], [], [1]).
```

In fact, *every* parameter appearing after the first inserted
code in any E₀ image is shifted to a strictly positive index.
Thus `([],[],[0])` is **not in the range of E₀**, so no
`G`—not even an arbitrary function, let alone an M-map—can satisfy
`E₂∘E₀ = E₀∘G`.

This is an obstruction to even the **forward** set containment
`π([∅,U]) ⊆ [∅,π(U)]` claimed in Lemma 4.1. It is not an
objection to the independently checked fat-tree Ellentuck theorem.
It shows that the paper's specific projection formula cannot
simply be adopted unchanged as a Lean theorem for this geometric
reduction relation. A *different* map, a restricted/cofinal
fat-tree order, or another transfer proof would be needed.

The standalone
[`check-fat-projection-free-ancestral-witness.py`](https://github.com/janhubicka/lean-successors/blob/successor-fat-projection-transfer-audit-20261016/scripts/check-fat-projection-free-ancestral-witness.py)
enumerates free-history levels and verifies the geometric inclusions
on the first five rows and the excluded target image. **The
full infinite reduction and nonfactorization have an English proof
above but are not yet a Lean-kernel-certified counterexample.**
The test is diagnostic, not a substitute for formalization.

The immediate next mathematical task is to formalize this small
counterexample in the actual `FreeAncestral.freeSMTree` instance
and to audit whether a **cofinal aligned subclass** of fat-tree
refinements suffices for the Ellentuck argument. Merely changing
`range(F_U) ⊆ T_U` to equality without proof would be incorrect:
fat lifts include additional parameter choices not represented
by the canonical shape-map image.

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

## Arbitrarily delayed obstruction: why the projection is not continuous

The same witness works **after any prescribed finite fat-tree stem**.
For each integer `q≥1`, let `V_q` agree with the fat tree U above
in its first `q` rows, and then insert a single extra target level
at target cut `q+1` using an ancestral parameter `[0]`;
all subsequent rows are identities. Its cuts are those of U
through index `q`, followed by U's cuts shifted up by one.
The geometric reduction index is

```text
  φ_q(i) = i        for i≤q,
           i+1      for i>q.
```

Before row q the fat lifts agree. At row q the ambient U is
already the identity fat tail: its lift across two ambient rows
reaches **every** successor history on the required later level,
and hence contains the V_q lift. After row q, both tails are
identity and all the one-lift inclusions are equalities.
Thus `V_q ≤_fat U` at every index and
`V_q.initialSegment q = U.initialSegment q`.

For the source history of level q with only empty parameter
codes, `F_{V_q}` appends code `[0]` after applying E₀.
No such history lies in `range(E₀)`, since E₀ shifts every
parameter of every old transition from `j` to `j+1`.
Therefore **none** of `F_{V_q}` factors through `F_U=E₀`.

This shows more than the failure of one neighbourhood equality:
**the original projection is discontinuous at U**, with the
fat-tree reduction/topology and shape-map right-composition
topology currently specified. The monoid basic neighbourhood
`[empty,E₀]` contains `π(U)`. Every fat basic neighbourhood
`[x,W]` containing U has a finite prefix `x=U|n`
and `U≤W`. Choose q≥max(1,n). Then `V_q≤U≤W`,
`V_q` extends `x`, yet `π(V_q)∉[empty,E₀]`.
So `π⁻¹([empty,E₀])` is not open around U.

The finite regression script checks the genuine lift inclusions
and excluded images for `q=1,2,3`. The argument for all q is
mathematically explicit above, but **is not yet an elaborated
Lean theorem**. No conclusion about the truth of Theorem 1.11
itself follows from this: it invalidates the current *proof route*
via this `π`.

Possible replacements include a newly proved transfer on a
suitably aligned cofinal fat-tree system, or a different
topological proof for the shape-map space. Imposing
`F_V=F_U∘G` as an extra condition in the fat reduction would
change that Ramsey space, so its A.3/A.4 and Ellentuck must
be reverified rather than inherited from the old proof.

## Verified identity-tail lift lemma

The next independent reusable ingredient is now proved in Lean
(PR #562, focused CI green at the pre-export head). For **every**
`SMTree H` and source cut `i`, the row extension of the
identity fat tree is *literally* `MMap.id H`.
Moreover, `identityFatTree_liftTo_full H i k` proves that
the geometric lift of the **entire** source level `i`
through any block of identity rows is the **entire**
target level `k`.

This is the exact reason the delayed parameter code
`[0]` remains geometrically legal in `V_q ≤fat U`:
the identity tail of U admits **all** ambient successor
codes, not only those in `range(F_U)`. The proof
uses `canonicalExtension_unique` to remove the
noncanonical representative of `AM.id1`, then the
unique predecessor at each later tree level.

The remaining Lean obligation is now a **relative**
identity-tail normalization for U with first row E₀,
followed by the already verified
`tailCoordinateRow_oneBlockOccurs` and
`splice_reduces`. This geometric construction must
still be completed to certify the actual infinite
noncontinuity witness and is **not** claimed by the
identity-tail lemma alone.
