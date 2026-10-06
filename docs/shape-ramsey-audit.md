# Shape-preserving Ramsey theorem: completion audit

This is the historical audit of the first direct proof. For the current two
proof routes, finite corollaries and regression checks, see
[shape-proof-routes.md](shape-proof-routes.md).

## Verified snapshot

The proof snapshot is `1856f22fa1c94a27b3b282945da7d0f962903cc6`.
GitHub Actions [run 37150740752](https://github.com/janhubicka/lean-successors/actions/runs/37150740752)
completed successfully: full library build, public-interface regressions, and
eight transitive axiom checks. The toolchain is Lean `v4.35.0-rc3`.
The artifact records the resolved dependency manifest rather than pretending
that the branch's `lake update` configuration is an immutable dependency lock.

Later commits add manuscript annotation tooling and this audit; their own
workflow results must be checked before calling those additional tests passed.

## Exact public conclusion

`SuccessorTree.SMTree.shapePreservingRamsey` in
`SuccessorTree/ShapeFiniteRamsey.lean` proves, for an `SMTree S`, natural numbers
`n,k`, a finite type `κ`, and an arbitrary colouring `AM H n k → κ`, that there
is a total map `W` in the distinguished monoid fixing all source levels below
`n` for which every finite composite `W a` has the same colour.

Here `AM H n k` is a realised finite restriction to the first `n+k` source
levels, with the first `n` levels fixed. `shapeActK` is literal left composition
followed by restriction. It is not a substitute action on just the selected
replay lines. The regression file also states the conclusion without the
`shapeActK` notation, using total-map composition and `toAM` explicitly.

The relative theorem `shapeRamsey_approximations` additionally gives a genuine
right-composition refinement below any prescribed frozen-prefix subspace.
Both the colour and the initial subspace are fixed before that refinement.
No extra local-pigeonhole, Ellentuck-amalgamation, or inverse-closure hypothesis
appears in the public theorem.

## Proof and failure-point audit

1. **Local versus global homogeneity.** M3/Hales--Jewett gives a monochromatic
   finite replay line. The direct large-set constructions in
   `ShapeMillikenFusion.lean` and `ShapeRamseyFusion.lean` obtain the full
   one-moving-level theorem. Merely declaring a replay line monochromatic
   would not establish this result.
2. **Canonical extension direction.** Canonical extensions are constructed
   using M2 gap closing and M1 fusion; uniqueness then follows from consecutive
   image levels and exact successor preservation. No equivalence between M2
   and existence/uniqueness of canonical extensions is asserted.
3. **Fixed bridge.** `ShapeLocalPigeonhole.lean` uses the same canonical prefix
   before and after a same-depth refinement. The repaired idempotence step is
   instantiated at the original finite factor, not at the already canonical
   extension. `ShapeExactFactor.lean` then accounts for every one-step child.
4. **Depth indexing.** An approximation through a last source level is not
   indexed by that level: the number of retained source levels is one larger.
   Front fusion at depth `d` freezes source levels strictly below `d`.
   The empty approximation is never treated as having positive depth.
5. **Preservation through fusion.** Earlier one-step decisions are hereditary
   under right-composition refinements. The fusion is a genuine reduction of
   every stage, not just a pointwise agreement on individual prefixes.
6. **Dimension induction.** `buildShapeProductStep` replaces each child colour
   with the common colour at its parent prefix. The relative induction acts
   below the resulting subspace. `exists_frozen_rightFactor` keeps its right
   factor in the correct frozen-prefix class, so the child-colour equation
   survives the final refinement.
7. **Representatives and boundary cases.** Finite composition is independent
   of the chosen representative on the source domain. Width zero is handled
   separately; width one invokes the already proved one-moving theorem.
   No nonempty-colour-type hypothesis is imposed: a colouring of the identity
   approximation supplies a default colour whenever one is needed.

## Trust boundary

`scripts/CheckShapeRamsey.lean` tests arbitrary palettes `Fin r`, the `n=k=0`
case, and the literal-composition interface. It prints transitive axioms for
canonical uniqueness, local replay, the global one-dimensional theorem, the
arbitrary-prefix pigeonhole, front fusion, the product step, the relative
finite-dimensional theorem, and the final AM theorem. CI requires all eight
reports and allows only `propext`, `Classical.choice`, and `Quot.sound`.
In particular, `sorryAx` and additional theorem axioms are rejected.

This is a kernel-checked theorem of the encoded `LevelTree`, `STree`,
`ShapeMap`, and `SMTree` interfaces. It is not a separate Lean proof that the
paper's set-theoretic tree definition is equivalent to the `LevelTree`
interface. Nonemptiness of each level is derived from M3. The represented
finite maps are restrictions of total monoid maps, as required by the intended
AM convention. These translation boundaries are marked explicitly in TeX.

No separate external referee or agent was invoked for this completion. The
checks above are proof-kernel checks, explicit regression examples, and this
mathematical dependency audit.

## Manuscript scope and delivery

The local execution service failed before it could open the uploaded
`successor-clean(2).tgz`. Its contents have therefore **not** been inspected,
modified, or compiled. A recoverable older `main.tex` supplied exact local
label contexts for the annotation patches. The patches preserve existing
prose and review notes; they do not replace the manuscript from that older
copy. The generator's `--root` mode reads an actual checkout and checks every
patch against those supplied bytes without modifying the checkout.

Green markers cover canonical uniqueness, the one-moving-level theorem, and
the finite-dimensional theorem. Orange markers deliberately limit the claims
for the general splitting proposition and the canonical-letter presentation
of the local pigeonhole. The tree interface gets a blue marker. All links are
pinned to the verified proof snapshot above, and all new inline notes begin
`Řehořek:`.

This completion does **not** certify the fat-tree Ramsey-space theorem, the
pointwise-Borel transfer, the composition-Ellentuck assertion, or later
applications and envelope bounds. Existing warnings about those results must
remain in place.

The artifact contains two Lean-repository patches. `shape-ramsey-completion.patch`
is relative to `ef5cce3d9dcfea768c69998515a7ded6bc03e603`; the broader
`shape-ramsey-branch.patch` is relative to the merge-base recorded in
`BRANCH_BASE`. Neither should be described as conflict-free on arbitrary
current `main`. The separate manuscript patches are for the TeX repository,
not the Lean repository. See `manuscript/README.md` for application commands.
