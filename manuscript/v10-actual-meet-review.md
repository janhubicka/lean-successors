# Exact H construction and actual meet checkpoint (PR 163)

Proof commit: `30b397e999b51a1355563ebe9e3b1c214cc60afb`.
Both full Lean run `38020379540` and focused V10 run `38020379541` passed.
The new audit has 29 endpoints (24 new, five imported unchanged from PR 160).
The downloaded logs were also checked locally: only `propext`,
`Classical.choice`, and `Quot.sound` occur. The three new Lean source files
match the audited artifact byte for byte.

## Statement and scope

`forbiddenFreeH_prefix_meet_charge` takes a finite normalized forbidden
family, a base L-structure K on Nat which avoids it, a positive generation
parameter k, and an arbitrary finite cutoff N. Nodes s and t are arbitrary
admissible prefixes of original types of vertices v,w<N in the constructed
finite H+. They have a common predecessor and their genuine LevelTree meet
is neither operand. Its level is iota(p,r), with 0<r<=k.

The theorem derives real representations of both originals, their positive
generations, the first complete binary disagreement, and membership of that
coordinate in BOTH E-socles. After exchanging originals the conclusion is
r=m<n<=k, p the first incident base neighbour p(i), and p+1<j. There is no
H-age, trace equality, free-cut bound, or meet-charge premise. H's partial
structure axioms and forbidden-free age are derived for one concrete object.

The files are HActualMeet.lean, HFinitePartial.lean, and HFiniteAge.lean.
KptMeetBridge.lean and KptMeetConverse.lean were imported from the checked
PR 160 unchanged. All files are included through the root HFiniteAge import.

## Adversarial checks

Both directed orientations and absent binary atoms are retained. Unary
and diagonal singleton data enter the complete type records. E is never
used as a forbidden L-atom. Fake vertices are L-isolated, not L+-isolated;
nonempty derived E-socles exclude fake and generation-zero originals.
Equal generations, including two top generations, cannot first differ at
positive generation. Originals with the SAME first index and different
generations are permitted and covered by the regression.

Nontrivial irreducible copies project in strictly increasing first-index
order. Non-neutral forbidden singletons are handled separately. Empty
binary signatures and empty forbidden families are allowed; the forbidden
pattern representation excludes the empty structure and neutral singleton.

These checks and a separately implemented regression were performed in
this continuation; no independent referee agents were invoked.

## Regression and reproducibility

The generator-based test compares complete induced L+ records and computes
maximum common prefixes independently of the desired formula. The identical
local and CI reports check 28,672 models, 6,549,504 original pairs, 53,184
positive-generation meets, 4,266,432 nontrivial prefix pairs, and 17,728
reverse-only charges. There are 2,838,528 pairs with different singleton
roots, correctly excluded by the common-predecessor premise. Finite testing
supplements the Lean proof and is not a replacement for it.

The focused workflow now derives build targets from the CheckV10*.lean
imports, audits every such file, and retains the sources, logs and regression
report as the v10-actual-meet-audit artifact. Its shell pipelines use pipefail.

## Manuscript boundaries

The exact normalized finite-initial-segment meet theorem is proved.
Identifying it with the literal manuscript still requires the exact-copy H
wording and the finite-language normalization dictionary. The maintained
original-pool parameter-closure invariant, actual local-age/crossing/signature
arguments, and global M2/M3 maps remain separate obligations. The final
big-Ramsey upper bound is not certified by this endpoint alone.

The cumulative TeX overlay replaces the corresponding managed notes while
preserving all four mathematical repairs. The updater passes its fixture,
idempotence, git-apply checks, and missing/duplicate-anchor negative tests.
The current author-edited V10 archive was not available as raw bytes, so no
claim is made that this continuation patched its main.tex or rebuilt its PDF.
