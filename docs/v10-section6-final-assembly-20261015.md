# V10 successor: final Section 6 proof ledger

Status: 15 October 2026. This is a **validation ledger**, not a
claim that Proposition 6.44 has been completely verified.

## Scope and frozen text

Validate successor v10 exactly as written, using the normalized
finite unary/directed-binary/diagonal Boolean record model for Lean.
Higher relation arities, axiom relaxation and future applications are
outside the present task. Keep author TeX proof prose frozen: use
Řehořek TODO notes and accurately scoped validation markers only.

## Verified ingredients

- Normalized Kpt M1--M3 and successor-tree Ramsey theorem.
- Actual selected closure source/target, no-I2 uniqueness, corrected
  B3 failure for non-skippable I3, finite L-only age witness.
- Lemma 6.53 relocation: chosen upper original labels have genuinely
  higher H-generation; no replacement by unrelated equivalent types.
- Observation 6.52: complete induced signature collision and sharp
  relabelling over higher original names.
- I1/I2 seed/parameter/original-meet normal form, parity of positive
  free E-cuts, real H meet charges and a common higher-name pool.
- Literal top-generation seeds from one root and its prefixes,
  cardinality at most q+1; strict and trivial I2 events handled.

The merged source modules include I3ActualHigherSignature,
I1I2RealEventCharge, HTopGenerationSeeds and
HHighOriginalNameEnumeration. All claims remain scoped to the
actual signatures and hypotheses of the exported Lean theorems.

## Pending actual-run bridge

- PR #422: each Algorithm 5.4 stage closure represented in one
  final original-name universe V.
- PR #430: real selected generation-r I3 levels, with I1/I2 excluded,
  bounded by R(H_r), where H_r counts high originals of V.
- PR #431: actual selected I1/I2 real-generation levels bounded by
  H_r through the common first-neighbour meet charge.

These PRs are not GREEN until exact-head Lean and transitive axiom
checks pass and the code is merged.

## Manuscript's remaining induction

Put q=|A|>0 and let k be the largest forbidden pattern size
(or k=1 for an empty forbidden family). For the *actual*
Algorithm 5.4 run set

    V = {c} union {i in I : free_C+(i)>0}
    R(t) = sum_{F in forbidden family} (t+1)^|F|.

For every 0<r<k let S_r be the real selected positions iota(j,r),
and H_r be the set of original *addresses* in V of generation
strictly above r.

1. Split S_r into I1/I2 event levels E_r and remaining I3 levels
   T_r. The run proves each selected level is interesting.
2. Charge E_r to first-neighbour images of H_r, proving
   |E_r| <= |H_r|.
3. For T_r use actual failed B3 and higher-generation chosen labels,
   giving |T_r| <= R(|H_r|).
4. Thus |S_r| <= |H_r| + R(|H_r|). Prove H_r is controlled by
   previously bounded *higher* generations plus root c.
5. Prove the top-generation base a_k=q+1: only q top seed prefixes
   may be selected at generation k. Rule out generation-k strict
   meets and I3 failures; seed count alone is not the base.
6. Discharge the explicit hypotheses of the already proved
   descendingGenerationCardinalityInduction_signature, with
   M_r=sum_{s>r}a_s and a_r=M_r+R(M_r).
7. With M=sum_{r=1}^k a_r, show the final closure lies in the
   meet closure of Y plus at most M original full types. Prove
   the forest meet-closure bound <=2(q+1+M), count positive I3
   levels by R(M), and add at most one level zero. The desired
   bound is b(A)=2(q+1+M)+R(M)+1.
8. Empty A uses the separate zero-height envelope convention;
   empty forbidden family gives R=0.

## Adversarial audit requirements

- Use the currently selected closure, never an enlarged all-eligible
  original pool when identifying the partial function f_ell.
- Keep **complete induced** lower-upper and upper-upper relations,
  including absent directed bits and unary/diagonal data.
- Finite forbidden B3 witnesses are L-only; do not manufacture E.
- Preserve the address of each named original, even when two
  originals realize equal partial types.
- Use the SAME final finite name universe for all stages and both
  I1/I2 and I3 counts.
- The eventual cardinal bound must count envelope levels, not
  merely original vertices.
- Recheck the exact end-to-end Lean theorem and #print axioms
  before marking Proposition 6.44 GREEN. The normalized language
  adapter and A3(2) equality caveat are separately tracked.
