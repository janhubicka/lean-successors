# Successor V10: prescribed predecessors, order transport and crossing successor

## Provenance and active continuation

Repository: `janhubicka/lean-successors`.
Recovered review checkpoint: PR213,
`52db2246e6fa305e7c87add25bde61fe84ab38b0`.
The supplied continuation bundle was recovered locally and its two current
manuscript-note files were checked against their exact Git blob IDs.

Parallel V10 work appeared during this continuation. The active source uses
the common prefix implementation from PR214/217, not two incompatible copies
of the same declarations. The adopted PR217 head is
`39f7448843f65cff218b5e4dab749b889c4b547c`. Its one-line witness-lifetime repair
was incorporated by an explicit two-parent merge into the continuation;
the theorem statement did not change and no other branch was overwritten.

PR219, branch `formalize-v10-prescribed-order-transport-20261011`, is checked at
`8d8620571360210ed00402bf0551760a415ee95a`.
PR222, branch `formalize-v10-prescribed-gap-successor-20261011`, is focused-audit checked at
`6a370791c67b184f9f8028d477fad124bf6432c3`.
Both remain draft and unmerged. A review-only continuation collects the
manuscript TODO changes; its final SHA is recorded in the bundle README.

## Exact scope

All results concern the normalized finite unary/binary Boolean L+ model and
the actual `PrescribedBoringData.prescribedKptSkip` on admissible Kpt nodes.
Its existing assumptions are unchanged: B1/B2 data, corrected finite L-age
B3, admissibility of prescribed targets on the source set, and ell > 0.
No compatibility condition on arbitrary pairs, new representation premise,
abstract prefix law, or successor law is added to the total map.

## Verified predecessor and order results

The common upper-prefix proof derives equality of the complete ell-prefix
along a comparable upper chain, hence derives the same matching/neutral
branch decision. For matching images it computes both literal constructors
with one prescribed source and one valid inserted cut, using the one-filler
prefix replica for the shorter node and complete-record independence. The
unmatched case uses the neutral prefix theorem. Below and across the gap,
all observed atoms are retained old L+ atoms. This includes both binary
orientations, absent atoms, singleton facts, E pairs and the distinguished
vertex. `prescribedKptSkip_prefix` therefore covers all predecessor cases.

`PrescribedKptOrderEmbedding.lean` adds four checked endpoints:

- `prescribedKptSkip_ancestor_level_bound`.
- `prescribedKptSkip_ancestor`: G(a|n) = G(a)|iota(n), where iota(n) = n
  for n < ell and n+1 for n >= ell. These are actual admissible ancestors.
- `prescribedKptSkip_prefix_iff`: G(b) <= G(a) iff b <= a.
- `prescribedKptOrderEmbedding`: the same concrete map as an OrderEmbedding.

Order reflection takes the admissible prefix of the longer source at the
shorter source's level, compares the two equal-level image prefixes under
a common image, and applies the already-checked injectivity. It does not
claim arbitrary coordinate deletion preserves admissibility. The order
embedding is not, by itself, a ShapeMap or a meet-preservation theorem.

## Below-gap and crossing successor -- GREEN

`PrescribedKptGapSucc.lean` contains two new endpoints:
`prescribedKptSkip_self_prefix_at_gap` and
`prescribedKptSkip_weak_succ_below_gap`. At a base level below ell, the actual
S-tree's parameter-level axiom puts every parameter below the base. The
base and parameter list are fixed. The original successor is a witness
below the mapped successor, using the self-prefix fact if its level is
exactly ell. Thus the intended conclusion at ell-1 -> ell is weak; equality
with the level-(ell+1) mapped child is not asserted. This module does not
use an assumed crossing law or above-gap parameter transport.

## Evidence already checked

PR222 focused V10 build/axiom run: 38110392855, proof and audit steps passed.
Artifact: 11691549317, SHA-256
`dc2a54417be20359dc9d61b9d5839e950eeccc11c0960df7892f8984cb453010`.
The archive hash and exact new source/check-script bytes were verified.
All 53 named V10 audit logs (530 endpoint reports) passed the strict
checker again locally, including both new weak-successor endpoints.
The active continuation adds sixteen named endpoints since PR213:
ten inherited full-prefix endpoints, four order/ancestor endpoints,
and two weak-successor endpoints. The alternative PR216's four reports
are separate evidence and are not counted in this active total.

PR219 full Lean run: 38110042997, success.
PR219 focused V10 build/axiom run: 38110042904, success.
Artifact: 11690664932, `v10-actual-meet-audit`.
SHA-256: `5efe796b284a7f1a493dfc6579c0c7a89e1753a7913e1a46ca9826dcbaa99353`.
The archive hash, exact new source and check-script bytes were verified.
All 52 named V10 logs, comprising 528 endpoint reports, passed the strict
checker again locally. The four new order/ancestor endpoints and ten
inherited prefix endpoints use only `propext`, `Classical.choice` and
`Quot.sound`; there is no `sorryAx` dependency or additional axiom.
The synthetic PR merge `bc309dff0c4c44d44b684fca8acc6153f1a6449b` has exactly
the head's source tree (empty file diff).

The original alternative upper-prefix implementation was also checked at
PR216 head `d0aa37a7588c1814723af5b62e3769ef20a1ec41`: full run 38109673143 and
focused run 38109673289 both succeeded. Its four named reports and exact
check script were audited from artifact 11690977486, SHA-256
`b974f51eca0ea1fed68f84b3ed3790d434847f31b6843ea2e32c07e8a9fc0fb6`.
PR216 was then closed without merging to avoid duplicate declarations.
Its source and evidence remain under `evidence/alternative-pr216`; they
are not imported by the active stack. This is separately written proof
code, not a claim that independent human or spawned referees reviewed it.

Nonfatal Lean warnings remain, including the existing module-import and
`if_neg` deprecation warnings. A passing build is not a warning-free build.

## Manuscript and patch discipline

Only the ninth managed TODO (the boring lemma) changes; the first eight
TODO groups remain byte-identical to PR213. The source updater continues to
recognize either `lem:boring` or `lem:local-age`, reject duplicate or
ambiguous anchors, migrate old managed markers, preserve unmarked prose
and author TODOs, and apply idempotently. The previous four mathematical
repairs and separate B3 source repair are neither changed nor reapplied.

Local tests are exact-file/annotation fixtures, not a fresh application to
the author's full manuscript. The updater's raw fixture log contains its
generic label "actual supplied main.tex"; here that input is explicitly a
synthetic test file. Metadata for `successor-v10(4).tgz` and the generated B3-final source was
recovered from the Library, but both raw-byte materialization requests were
rejected as unauthorized for these Project-backed files. No complete source
bytes were obtained, so no regenerated manuscript archive or fresh TeX
compilation is claimed. See `evidence/source-recovery-boundary.json`.
The cumulative bundle is a Lean/review overlay with an incremental patch
from the exact PR213 file baseline, not a standalone repository.

## Remaining proof boundaries

1. Agreement with f on its source domain must be an equality of the complete
   L+ record, not just its L-reduct. Parallel PR218 stages an L-reduct lemma;
   it is not integrated or claimed as full agreement in this stack.
2. For successor bases at or above ell, transport the canonical
   empty-or-singleton parameter and exact terminal Sigma letter with the
   same concrete map, then use the proved uniqueness of decomposition.
   Parallel PR220 stages a finite terminal-letter lemma on a different
   branch; it is not imported here or a substitute for the global law.
3. M2 still needs necessity/decomposition for corrected B3. M3 still needs
   the repaired age test for its actual duplication prescription.
4. Reconcile I3/signature witnesses with finite L-structures and complete
   the language adapter before certifying the final upper bound.

The full prescribed boring extension lemma and final upper bound remain
OPEN. The proof checklist and validation overlay preserve that distinction.
