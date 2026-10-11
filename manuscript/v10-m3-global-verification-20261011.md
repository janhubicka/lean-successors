# Successor V10 — concrete M3 duplication checkpoint
Date: 11 October 2026. This is a cumulative verification/TODO note.
**The author's main TeX, four historical repairs and corrected-B3
statement remain frozen.** Do not convert pending proof candidates to
GREEN before exact-head Lean and transitive axiom checks pass.

## Proof architecture

Let n<ell and let a be an admissible Kpt type of level ell. An
actual forbidden-free finite witness A,v of a has freeLevel_A(v)=ell.
Insert at ell a clone of the earlier ordinary vertex n with
free cut d=freeLevel_A(n). The inserted L column has the complete
old n singleton and old-to-lower directed atoms below d; both
directions on lower [d,ell) are absent. For an old upper vertex u,
the new L pairs are copied from n only if ell<=freeLevel_A(u).
This is the essential E3 gate.

Irreducible forbidden copies containing ell only require correct
upper copying on vertices ACTUALLY linked to ell. They project
order-preservingly to an old copy replacing ell by n. Copies
avoiding ell pull back through IsLInsertion. The corrected
finite-L age test never assumes an E-structure on arbitrary witnesses.

## Exact verification evidence

- PR #241, head `92239569`: full Lean and focused V10 named-axiom
  audit passed. The literal E3-gated finite insertion is certified.
- PR #242, latest checked head `a364dcc8`: full Lean and focused V10
  audit passed. Linked-only irreducible forbidden-copy projection
  is certified.
- PR #243, latest checked head `d6462025`: full Lean and focused V10
  audit passed. The actual insertion satisfies that linked-only
  projection interface.
- PR #245: focused V10 audit passed after a target-size elaboration
  correction. Root workflow must be checked separately.
- PR #246: full Lean and focused V10 audit passed, including genuine
  admissible source-restricting output in the new finite model.
- PR #244: full Lean passed; its separate exact-head focused audit
  was still in progress at this checkpoint. Its dependence also
  compiled in PR #246, but track the own named endpoint report.
- PRs #247 and #248: finite terminal-letter and shortened
  parameter comparisons staged; earlier missing shifted-address
  simplification was repaired and propagated. Latest exact-head
  audits pending.
- PRs #249 and #251: finite canonical Kpt step and old ordinary
  E-free-cut/lower-column coherence staged, pending exact-head CI.

## New global candidate stack — NOT YET CERTIFIED

- #252 `M3OutputB2.lean`: compatibility of the COMPLETE ordinary
  L+ output socle from compatible sources, across different
  finite witnesses and type vertices. Checks both directed/absent
  L relations and every ordinary E pair. No fixed free cut
  across incompatible source classes.
- #253 `M3TotalPrescription.lean`: choose an actual finite
  representative for each admissible level-ell T and form its
  complete shifted type. Source is ALL admissible T. Proves B1,
  B2 and target admissibility; arbitrary values outside source
  are irrelevant.
- #254 `M3ActualB3.lean`: derive corrected finite L-only B3 for
  that exact selected prescription: ordinary lower clone data
  plus upper terminal-letter copying, then irreducible projection.
  Do not replace this with the old E-witness necessity lemma.
- #255 `M3OneGapShapeMap.lean`: apply the previously verified
  prescribed boring extension to the actual M3 data to obtain
  a KptM ShapeMap skipping only ell.
- #256 `M3DuplicationEndpoint.lean`: require the actual admissible
  Kpt successor with the canonical empty/singleton parameter list
  and terminal letter copied from T's earlier n-th crossing.
  This is the complete normalized-model M3 axiom candidate.

**Verification is only complete if the last exact-head focused
module build and transitive axiom audit pass with no sorryAx or new
nonstandard axioms; a successful unrelated root build is not enough.**
All five branches remain draft at this checkpoint.

## Adversarial findings and repairs

- Unconditional copying to every upper old vertex is false. If an
  old upper vertex's E-free cut lies before ell, the new inserted
  relation must be absent even when its pair with n was present.
  Hence linked-only upper projection is mathematically essential.
- The duplicate's cut d(T) is source-dependent, though old
  ordinary L+ compatibility determines it inside a compatibility
  class. No global cut is assumed.
- The normal-form predecessor/terminal inputs must compare complete
  L+ records, not merely the L-reduct, and the level-zero
  parameter case must be genuinely empty.
- Lean elaboration repairs so far: explicit upper-address
  inequality, target carrier-size equality, explicit shifted
  vertex removal and strict E-spacing in the B2 new loop.
  These repairs change no theorem hypotheses.

## Still outside M3

M2 corrected-B3 necessity/decomposition, I3 finite-L signature
witnesses, the full original-language adapter (including
diagonals and nullary relations) and the final big-Ramsey upper
bound remain unverified. On confirmation of M3, the next
priority should be M2, not another implementation of M3.

## Editorial policy

Only the ninth managed TeX TODO may be updated with the verified
M3 boundary. The other eight review groups, unmarked author prose,
original mathematical patches and existing author TODOs are
byte-frozen. No merge of unverified draft PRs.
