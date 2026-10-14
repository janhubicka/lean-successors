# Successor v10: remaining validation in the existing axiomatic setting

**Review checkpoint: 14 October 2026.** This note audits the current
manuscript statements and their checked Lean endpoints. It does **not**
propose weakening or generalizing M1--M3, and it is not a replacement
for the frozen author proof. Source changes to that proof require
editorial approval; add only labelled TODOs and validation markers.

## Main checked proof route

- The abstract successor-tree Ramsey theorem has two checked Lean
  proof routes: direct fusion in `ShapeFiniteRamsey.lean` and
  fat-tree Ellentuck in `ShapeEllentuckRamsey.lean`. Their shared
  finite-dimensional induction is in `ShapeFiniteInduction.lean`;
  the required one-dimensional inputs remain separate.
- The fat-tree A1--A4, finitarization, splice, fat Ellentuck and
  shape correspondence have checked named endpoints. The optional
  embedding-space EA claim is *not* an input to these results.
- Section 5's finite-envelope closure, interesting-level
  independence and minimality endpoints are checked (see
  `EnvelopeTheorem.lean`). The manuscript still needs precise
  explanations at the finite-prefix factor step, the nonempty
  top case, the example of nonuniqueness and the A3(2)
  neighbourhood equality-versus-inclusion issue. These are
  editorial TODOs, not reasons to change the axioms.
- The normalized Kpt S-tree has actual M1--M3, with M2 derived from
  the corrected finite L-only compatible B3 non-edge proof and
  literal M3 from its concrete duplicate map. The full
  `normalizedKptSMTree` and its direct/Ellentuck Ramsey
  specializations have passed full Lean and standard-axiom audits
  (PRs #381--#383, integrated into main).
- The exact normalized H+ finite construction, actual meets,
  positive-generation meet charging and original-pool closure
  budget have checked independent endpoints in
  `HFinitePartial.lean`, `HFiniteAge.lean`,
  `ConcreteOriginalPool.lean` and `HClosureCharge.lean`.

**Scope boundary.** These certificates do not automatically
validate the original manuscript's full Section 6 upper-bound
recurrence. Its actual age-signature and selected-level inputs
must still be checked.

## Remaining Section 6 statements, in logical dependency order

1. **Condition (I3) and finite forbidden-age witnesses.**
   If the prescribed insertion passes B1/B2 but fails the
   corrected compatible B3 test, extract an actual *finite L-only*
   witness W with the exact initial C+ L-socle through ell,
   prescribed complete upper crossings, a forbidden ordered copy
   e whose image meets ell, and W without ell forbidden-free.
   Do not introduce E on W; all chosen upper original labels
   come from the ambient original pool `V_I`.
   The local-age and prescribed-construction Lean modules provide
   the finite insertion and upper-type formulas, but the full
   I3-to-original-pool interface is not yet a named endpoint.

2. **Observation 6.52, uniqueness of signatures.**
   Signature values are either bottom on the *lower* part of e
   or names of ambient original vertices from its *upper* part.
   Choose the latter from the actual source data and derive
   complete prefix-type equalities, including reversed and
   absent binary tuples, unary and diagonal data. The ordered
   splice from `SignatureSplice.lean` and
   `ActualCrossingSignature.lean` then gives a forbidden copy
   in the later witness avoiding its tested coordinate.
   `ChosenAgeSignatures.lean` (PR #387) attempts to eliminate
   manually supplied cut/type/signature fields from this
   collision argument; check exact-head Lean and its axioms before
   marking that candidate green.

3. **Lemma 6.53, generation of an (I3) level.**
   The lower part of e is a nonempty proper initial segment of
   length r, and its last vertex ell must have generation r-1,
   strictly below the maximal generation k. For each non-bottom
   signature value v, show generation(v) > r-1.
   The manuscript's relocation argument replaces lower
   \(\iota(j_a,n_a)\) by \(\iota(j_a,a)\).
   The checked order/incident-tuple relocations are in
   `RelocationIrreducible.lean` and related modules. The missing
   composed endpoint must use the actual I3 witness and derive
   its generation conclusions; finite diagnostic enumeration
   cannot substitute for this theorem.

4. **Proposition 6.44, complete induction.**
   For a fixed nonempty source of size q, the manuscript defines
   \(R(t)=\sum_{F\in\mathcal F}(t+1)^{|F|}\), \(a_k=q+1\),
   and recursively for r=k-1,...,1,
   \(M_r=\sum_{s=r+1}^k a_s\) and
   \(a_r=M_r+R(M_r)\). The charging theorem bounds levels
   selected by (I1)/(I2) by \(M_r\); Observation 6.52 and
   Lemma 6.53 bound (I3) choices by \(R(M_r)\).
   Complete the induction, account for generation-zero
   levels, and derive the advertised envelope bound. The
   final closure-count and q=0 conventions must be explicit.

5. **Theorem 6.26.** Only after the numerical bound is checked,
   apply the already verified abstract successor-tree Ramsey
   theorem to the finitely many approximation/embedding types
   represented below that bound. This is a transfer/application
   step, not a missing assumption in abstract M1--M3.

## Manuscript policy and maintenance

- The author mathematical text and the four previously approved
  repair patches remain frozen. All remaining corrections go into
  the nine managed v10 TODOs / validation markers and separate
  review notes until editorial decisions are made.
- Green requires an exact matching theorem statement, Lean build
  and transitive axiom report with no `sorryAx` or new axioms.
  Avoid conflating an abstract conditional lemma with an actual
  constructed witness.
- No higher-arity adapter, alternative successor axiomatization,
  EA strengthening or general-paper work belongs in this pass.
  Record possible future weakening points separately after the
  current draft's stated results are validated and cleaned.

The highest priority is the finite I3 witness and its ambient
original labels; it is the input used by both signature uniqueness
and the generation recurrence.
