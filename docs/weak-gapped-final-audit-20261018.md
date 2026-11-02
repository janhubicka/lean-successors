# Final adversarial checkpoint: weak gapped fat trees (18 October 2026)

**Verdict:** Current M1–M4 do not imply the marked fat-tree A4 Ramsey theorem. Keep this as a draft branch; **do not merge or mark a global weak theorem Lean-verified**. The strong-tree Ramsey and envelope applications remain unchanged.

## Two independent obstructions

**(1) A4 is false under the natural full marked-word reduction.** Let M_odd be the parity-restricted ordered-word monoid in Appendix B: canonical blocks contain an odd number of occurrences of their variable and an even number of constant 1's; arbitrary initial constant heads are allowed. M_odd satisfies M1–M4 with the singleton designated neutral alphabet {0}. Moving cutting marks preserves the *odd variable count* of each block, but NOT its constant-one parity. Among the first three odd counts after block 0, two have the same residue modulo 4. Group the first four complete marked blocks, keeping the live variable in block 0 and those two, substituting 0 in the remaining block, and take the next cut at the old right cut after block 3. The selector itself is globally admissible, the infinite tail is unchanged, and the first new block has variable multiplicity m0+2 mod 4. This gives two different first-row colours below every marked word. Thus A4 fails at the empty stem. The full unrestricted ordered-word Carlson theorem remains a valid separate positive benchmark.

**(2) Locally extendible width-two rows do not model all legal marks.** The globally allowed canonical parity blocks `x11` and `x` concatenate to `x11x`. The cut `x1 | 1x` is legal between variable supports but forces the first width-two local row to have variable block `x1`, which violates even constant-one parity and has no extension in M_odd. Hence `GappedFatTree` defined with a row in AM^(c_i)_2 is only a *locally extendible subspace* for a restricted monoid, not the desired all-marks space. Global coherence/partial live-profile states across a cut will be necessary.

These are distinct from the old direct-monoid Ellentuck counterexample.

## Formal evidence

Focused Lean run [39158359350](https://github.com/janhubicka/lean-successors/actions/runs/39158359350) **passed** for proof commit `c48924acabb5f6070ea54bba81fb5ef158fb2fce`: 47 exact named theorem/axiom reports; only standard Lean axioms; code-admission/source-axiom scan green.

- `SuccessorTree/Block/MarkedParityExact.lean`: arbitrary-cut four-block construction with no unjustified individual constant-parity premise.
- `SuccessorTree/Block/MarkedOddWordA4.lean`: an actual infinite tail-carrying four-block word transformation and a formal negation of root A4 for any reduction relation containing the three explicit legal selector transformations.
- `SuccessorTree/Block/MarkedCutNonlocality.lean`: global `x11x` and inadmissible split `x1|1x`, with exact syntactic proofs.
- `SuccessorTree/FatTree/GappedReduction.lean`: the all-interval geometric preorder (identity, transitivity and target-cut lifting) on the locally extendible prototype, using the existing strong `SMTree` as a temporary source of AM/canonical completions.

**Lean boundaries:** The full weak-monad/monoid `M_odd` is not yet constructed as a Lean instance of a weak `SMTree`; the new infinite A4 kernel assumes the reduction contains the explicitly defined four-block moves. The English full marked-word definition does contain them. A1–A3 for the proposed truly globally marked weak successor-profile space have not been formalized. No unsupported green marker is assigned to that theorem.

Independent finite diagnostic: `test_marked_odd_reduction.py` exhaustively checked **104,976** quadruples of odd-variable marked blocks of length at most 3 and both binary evaluations: legal selector, exact span containment, odd new variable count, and opposite mod-4 residue.

## Manuscript

Reviewed incremental patch `manuscript/weak-axioms/weak-validation-nonlocal-cuts.patch`, against the last reviewed 71-page gapped-fat-row source, inserts a localized observation and proof of (2), and qualifies the local row example as belonging to the unrestricted word monoid. The 72-page corrected PDF and real LaTeX redline were built; exactly the five inherited overfull warnings remain, no undefined references/citations. The user has the patch/PDF/review pack as conversation artifacts.

## Next viable direction

First choose the actual desired object: locally extendible gapped fat trees (strict subspace) or globally coherent marked fat trees with arbitrary marks. The user explicitly requests the **latter**. Its finite approximations must store open/partial line states and marks jointly, without requiring separate monoid completions. Next identify a minimal colour-free *separating* neutral alphabet or live-variable-profile richness condition (e.g. one that sees both 0 and 1 for binary words) excluding M_odd, and prove a relative marked all-front lemma. Under the current axioms, a positive global A4 proof is impossible. Do not substitute A4 itself as an axiom.

Carlson-style extracted words via nonadjacent selected lines are explicitly deferred. Keeping the original strong M2'/M3' envelope theory is intentional.
