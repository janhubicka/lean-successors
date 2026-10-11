# V10 prescribed insertion: verified finite representation independence

## Proof checkpoints

PR #205: `538490affc77c23e3704cc4235d78972bda37757`.
Full Lean run `38096247781` and focused V10 run `38096247806` passed.
Artifact `11685969263` was downloaded and checked against SHA256
`023a8cbf7eefb665d4abef2fc5be85e07f0daf6c1ed75d1cce67881dad02ab1f`.
All six new axiom-audit endpoints occur; their dependencies are a subset of
`propext`, `Classical.choice`, and `Quot.sound`. The compatibility-existence
result uses no axioms.

PR #206: `4fc409b368a50caf084ef5696203927f2cd59968`.
Focused V10 run `38096396531` passed. Artifact `11685849892` was downloaded and
checked against SHA256
`4613ae947c4f97fab004dfdeb9f1be3628a184b40e9f4c027fd69c8a1af79b37`.
All three new theorem endpoints use only the same standard Lean axioms.
Full Lean run `38096396547` was still running when this checkpoint was written;
its status is separate from the successful focused proof/axiom audit.

Both proof PRs and manuscript PR #207 remain draft and unmerged. This increment
continues green PR #203, not the earlier stale #199 status. The downloaded prior
artifact uses CI merge `e303cad08daa77a6717eff9b7d2e8263f55ea8f9`; a live GitHub
comparison with PR203 head `fe1d91e39a954eadf5676dd1863ad424d1aa6106` confirmed no
file differences.

## Mathematical scope

The gate `ell <= freeLevel(u)` is visible in the complete source type: for
ell > 0 it is exactly `E(ell-1,u)`, while ell = 0 is handled separately.
Complete longer records recover the shorter source types at every ordinary
coordinate and at the distinguished vertex, including when that vertex has
different indices in two ambient realizations. Compatibility, selected lower
columns and both gated incident directions are independent of the ambient
witness. No target value outside the prescribed source is used.

The full inserted L+ record is therefore independent of the ambient witness,
including every directed positive or absent L-atom, singleton data and all E
pairs. It is identified definitionally with extraction from the genuine finite
`prescribedInsertPartial`. Compatible prescribed-output representatives may
also vary: equality of their lower columns and inserted E-cuts follows from
ordinary-socle compatibility, rather than being separately assumed.

## Manuscript and next step

The cumulative overlay now marks these nine finite independence endpoints
GREEN, but the global prescribed ShapeMap, M2/M3 uses, I3 reconciliation and
final upper bound remain OPEN. The source updater now accepts the actual
`lem:boring` anchor or its legacy `lem:local-age` alias, rejects ambiguous or
duplicate anchors, and preserves unmarked author prose and TODOs. All local
fixture, idempotence and patch-application tests passed. The actual current
V10 archive was not available for a fresh source application or TeX compile.
The four prior author mathematical repairs and the separate B3 repair are not
reapplied or altered by this annotation update.

The immediate next proof task is to retain the literal constructor identity,
or inserted type record, in the conclusion of the matching finite witness
existence theorem. Its proof already constructs `prescribedInsertPartial`;
its current existential statement forgets that identity. Preserve it together
with forbidden-age avoidance and transported free cut, then use the new
independence theorem to define a total map on admissible Kpt nodes. After
combining matching and neutral branches, prove prefix/injectivity laws and
transport exact successor parameters and terminal letters. The crossing at
ell-1 requires only the weak successor statement, not exact equality.

The repaired B3 is a finite common-socle L-age test. The old third condition
of `lem:comp` does not supply it for M2, and the actual duplication prescription
still needs its M3 age test. None of those bridges follows from the newly
verified finite representation independence or from the checked neutral map.
