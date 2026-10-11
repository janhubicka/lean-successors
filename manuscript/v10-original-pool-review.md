# Concrete original-pool invariant and closure meet budget (PR 164)

Proof checkpoint: `d2fad6fcafe9f40f278fc2cff22986af6b3ef2dd`.
Focused Lean build and transitive axiom audit: run `38051214553`, passed.
All 16 new endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.
The downloaded artifact SHA256 is
`cd6fbbbc6048276d4252610223cb932158b109ce2608cb21482db7ce91850bba`.
Its new Lean sources match the delivered local sources byte for byte.
All four downloaded audit logs were rechecked locally: 16 new endpoints,
29 actual-meet endpoints, 284 earlier V10 endpoints, and nine incident endpoints.
The final-head full-build status is recorded in the PR discussion.

## Statements and assumptions

`ConcreteOriginalPool.lean` derives the actual empty-or-singleton parameter
along any represented prefix from the admissible Kpt successor graph and
the unique E cut of its new ordinary vertex. All L+ facts are retained.
Originals are indexed by ambient vertex addresses, so identical types do
not incorrectly identify their origins.

For any selected set I and seed address set U in a genuine forbidden-free
finite ambient A, define V(I) as U together with selected vertices whose
free level is positive. The endpoint
`admissibleKpt_stage_closure_subset_pool` proves that the actual Section 5
closure stays represented by V(I), provided its initial types are represented
by U. It assumes neither parameter closure nor a canonical decomposition
interface. This is the stage invariant, not a proof of every clause in the
manuscript's arbitrary-Z characterization.

`HClosureCharge.lean` applies this invariant to the constructed finite H+
and combines it with the checked actual prefix-meet charge. Both originals
are in V(I). A fixed higher-generation original has a unique least incident
base neighbour, so it determines at most one charged level at each positive
generation r. `forbiddenFreeH_closure_meet_budget` supplies a finite image
budget of size at most the number of eligible higher-generation originals.
Eligibility excludes originals without an incident base predecessor. The
default in the total index function is never used for an eligible original.
No parameter-closure, numerical trace, H-age, or charging premise remains.
The forbidden-free base, initial support, common-component and nontrivial-
meet hypotheses are explicit.

## Regression and review

The independent Python test extracts crossing parameters by reindexing
complete successor records and saturates by actual componentwise meets and
selected parameters. It does not use the expected parameter formula to
define the extracted parameter. Local and CI reports agree: 1,052 models,
125,280 stages, 3,928 crossings, 1,536 added closure nodes, and 192 checks of
representing original pairs for nontrivial meets. There are up to two
productive rounds followed by a stability check. All selected sets and
singleton seed addresses are tested; binary tables are exhaustive at sizes
3/4 and sampled deterministically at size 5, with four singleton assignments.
Finite testing supplements the kernel proof.

A negative example has free cuts (0,0,1,0,3), the only directed L-pair (0,2),
seed address 4, and selected level 2. Closure adds original type 2, then the
root meet. Retaining only seed 4 fails; the stage pool is correctly {2,4}.
No independent referee agents were invoked.

## Cumulative manuscript update

The overlay marks the concrete stage invariant and positive-generation
closure meet budget GREEN in the exact normalized model. The updater now
places a targeted replacement at cor:meet-origins and the previously unplaced
language-normalization note at thm:zucker. It preserves the four mathematical
repairs and all unmarked prose. Eight-group fixture, git-apply, idempotence,
missing/duplicate-anchor and malformed-note tests pass locally. Same-line
duplicate labels are now rejected; commented labels are ignored.

The author-edited main.tex is not present, so the deliverable is the
committed cumulative overlay and source-safe updater, not a rebuilt PDF
or a claimed applied patch to the unavailable manuscript.

## Remaining obligations

Identify the algorithm's exact seed types and selected sets, finish the
literal-language/exact-H wording adapter, the local-age/crossing/signature
arguments, global M2/M3 maps, and final Ramsey assembly. The original-pool
stage invariant and positive-generation closure meet budget are no longer
assumed inputs in the normalized model.
