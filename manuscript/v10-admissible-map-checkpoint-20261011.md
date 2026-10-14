# V10 checkpoint: admissible prescribed images and total node map

Continuation of PR207, observed on 11 October 2026 UTC.
Repository: `janhubicka/lean-successors`.
All changes remain on stacked draft PRs; no merge or main-branch write was made.

## Proof checkpoints

| PR | Exact proof head | Scope | Focused build and axiom audit |
|---|---|---|---|
| 208 | `d19b33ac038ac8f5d57f2ca0b46906573c373600` | Constructor-preserving finite existence; actual admissible matching images; graph uniqueness | Run `38097927654`: success |
| 209 | `01c0f06f041c93ecf0df6c458c0907fe71b4d729` | Unique matching selector and total prescribed-or-neutral node map; branch and exact level laws | Run `38098052917`: success |

Both separate full Lean workflows also passed: PR208 run `38097927695`
and PR209 run `38098052932`. Their full build and regression checks are
separate from the focused V10 builds and transitive named axiom audits.

The exact-head downloaded artifacts are:

- PR208 artifact `11686292006`, SHA256
  `f394bdcb9c2ee6d296289bf2e3e1c4dd9b1621c4eed40bd655b83eeb456f2f87`.
- PR209 artifact `11687027652`, SHA256
  `4f93c35b108a5fa0d3445ab81ba74ab9d0777a0e80442ca1cb94d9b10f164cc3`.

Both hashes match GitHub metadata. Both audit scripts in PR209's artifact
match the committed/local scripts byte-for-byte. The strict endpoint checker
verified all sixteen requested reports: fifteen new theorem endpoints and
one recheck of the backward-compatible existential API. Their dependencies
are contained in `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx` or additional axiom. PR208's six reports were also checked in
its own artifact. The build logs explicitly name the new modules and
end in successful completion.

## What has been established

`matching_prescribed_constructor_exists` strengthens the conclusion,
not the premises, of the previous finite theorem. It retains the actual
insertion cut and literal `prescribedInsertPartial` constructor, together
with forbidden-family avoidance, the old L-embedding, and transported
free levels. The old existential theorem is a corollary, not a duplicate
construction.

`matching_constructor_of_correctedB3` derives this witness directly from
the repaired source-level finite L-age condition. `matchingKptImage_exists`
then produces an image in the genuine admissible Kpt node set at level
n+1. `matchingKptImage_graph_unique` permits different finite ambient
models, different distinguished vertex indices, different compatible
source representatives, and initially different insertion cuts. Equality
of the necessary data is derived; it is not supplied as a new hypothesis.
Uniqueness itself does not use corrected B3 or target admissibility.

`prescribedKptSkip` is now a total function on the actual admissible node
set. Below ell it fixes the node. At and above ell, it uses the unique
prescribed image when the node's ell-prefix has a compatible prescribed
source, and the previously verified neutral image otherwise. The inputs
are B1/B2 data, corrected B3, admissibility of prescribed targets on the
source set, and ell > 0. Target values outside the source set have no
admissibility requirement.

The checked level formula is n below ell and n+1 at or above ell.
The two upper branch specifications, agreement with any literal matching
image, omission of ell, equal-level preservation and strict numerical
level monotonicity are also checked. This is not node injectivity or
preservation of the tree order.

## Manuscript annotations and local tests

`v10-cumulative-validation-status.tex` updates only the managed review
notes. The earlier eight grouped TODOs are retained, and the existing
boring-lemma TODO now distinguishes the verified total node map from the
unproved prescribed ShapeMap. It contains precise suggested wording for
constructing the map from a finite representative and its complete
inserted L+ type.

The four earlier mathematical repairs and the separate corrected-B3
source patch are preserved, not reapplied. The source updater and its
regression harness are unchanged. Their synthetic fixture tests passed:
real `lem:boring` and legacy `lem:local-age` anchors, ambiguity rejection,
idempotence, exact patch application, TeX-comment handling, and preservation
of unmarked author prose and TODOs. Those tests are not an application to
the full current author manuscript. Some fixture reports use a generic
`source_kind` label; the test scope is the synthetic fixture.

The current raw author archive is not available in this session. No fresh
full-manuscript update, TeX compilation, or locally compiled Lean workspace
is claimed. Lean checking was performed by GitHub Actions at the exact
proof heads above. The continuation bundle is not a full repository or
manuscript archive.

## Next obligations

Use the concrete `prescribedKptSkip`, not an abstract interface that assumes
its desired properties. First establish agreement with f on the source
set and full predecessor compatibility. For node injectivity, recover all
retained old L+ atoms in prescribed/prescribed, neutral/neutral and mixed
prescribed/neutral comparisons. Then transport the canonical successor
parameters and terminal letters, treating the weak boundary law at
ell-1 -> ell separately from exact successor equality above the gap.

An immediate useful adapter is avoidance for any valid canonical insertion
cut: compare it with the existential cut using ordinary-socle uniqueness,
then substitute. This should allow a representation theorem for the chosen
matching image analogous to `neutralKptImage_eq_of_representation` and a
prefix proof via `prefixReplicaPartialStructure`. These are next proof
steps, not checked endpoints in the present PRs.

The detailed case list is in `v10-prescribed-map-next-obligations.md`.
M2 still needs a necessity or replacement decomposition argument for
corrected B3; M3 needs its actual duplication age test; I3/signature
witnesses must be reconciled with finite L-structures. The normalized
Boolean-language adapter and final upper-bound assembly also remain open.
Neither the full prescribed boring extension lemma nor the final
big-Ramsey bound is certified at this checkpoint.
