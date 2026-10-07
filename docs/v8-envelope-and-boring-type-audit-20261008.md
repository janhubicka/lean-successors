# Successor-tree manuscript v8: continuation of verification (8 October 2026)

## Precise status of the Lean formalisation

The independent direct and fat-tree/Ellentuck proofs of the finite-dimensional
shape-preserving Ramsey theorem are integrated in `janhubicka/lean-successors`
(`#100`, `#102`). The branch for the manuscript's Section 5, *Envelopes and
embedding types*, is [PR #107](https://github.com/janhubicka/lean-successors/pull/107)
with verified source commit
[`0dc4dc4`](https://github.com/janhubicka/lean-successors/commit/0dc4dc4d7fb7169ea3acd4461ef734df2c5b0169).
Its complete repository CI run
[37657309674](https://github.com/janhubicka/lean-successors/actions/runs/37657309674)
and focused envelope check
[37657309826](https://github.com/janhubicka/lean-successors/actions/runs/37657309826)
both succeeded. The focused check audits 30 declaration endpoints and admits no
`sorryAx`; only the standard Lean axioms occur.

The genuinely checked content includes finite parameter/meet closure;
one-level (E1) pullback; the closure of prefixes; both branches of the exact
algorithm invariant; extraction of a one-level skip from a competing envelope;
finite-approximation competitors; minimality and height; independence of the
selected levels; a **separate** induction for independence of embedding types;
and existence of a complete finite algorithm run.

Verified declaration links for manuscript markers:

| Manuscript claim | Lean endpoint(s) |
|---|---|
| Observation `obs:closure` | `Envelope.envelope_closure`; finite competitor: `Envelope.prefixEnvelope_closure` |
| One-level punctured-prefix pullback | `Envelope.subset_range_of_oneLevel`, `Envelope.preimage_eq_of_oneLevel` |
| Lemma `lem:invariant` | `AlgorithmRun.fullInvariant` / `StageFullInvariant` |
| Minimality for finite competitors | `AlgorithmRun.minimal_output_height_AM` |
| Independent selected levels | `AlgorithmRun.I_eq` |
| Independent embedding types | `AlgorithmRun.embeddingType_eq` |
| Algorithm run exists | `Envelope.algorithmRun_nonempty` |

These are theorems about the typed `SMTree` interface. A literal equivalence
adapter for the manuscript's set-theoretic tree definition is **not** supplied;
no validation mark should suggest otherwise. The separate optional topological
projection for the composition space is still not part of this certificate.

## Section 5: required manuscript changes

The supplied `annotate_successors_v8.py` makes only additive `\todo[inline]`
notes and targeted validation markers, with a single unambiguous variable-name
repair described below. It deliberately leaves proposed substantive changes
for the authors to accept.

1. **The empty set.** Handle the algorithm's return `(Id, emptyset)` and height
   zero separately. The Lean `AlgorithmRun` for a selected top level is the
   nonempty branch; a full proposition marker must reflect that distinction.
2. **The finite-prefix form of Observation 5.7.** Minimality compares against
   `AM` envelopes as well as total monoid maps. The former require the verified
   `prefixEnvelope_closure` lemma; the total-map statement alone is not enough.
3. **Lemma 5.8.** Include in the invariant that `F_i` fixes levels below `i`,
   required in the noninteresting branch. The formalisation establishes the
   stronger `StageFullInvariant`.
4. **Claim 5.9 / local inverse.** For an intermediate prefix first prove
   `a|_j in H_i[T]`; set `j=ell(a)` to infer membership for `a`. The inverse
   is determined by crossing data, using (E1) and successor injectivity.
5. **Minimality's competing prefix.** Restrict the competitor at the **first
   input level `m'` whose image crosses `i`**, not at the overall competing
   envelope height `m`. Only then apply shape splitting twice to isolate the
   one-level map omitting `i`.
6. **Independence of embedding type.** Independence of the interesting-level
   decisions does not imply equality of `F^{-1}[X]`. Use the separate downward
   induction and one-level inverse uniqueness (`AlgorithmRun.embeddingType_eq`).

## Section 6: a concrete obstruction to the printed proof

Let the alphabet be `Sigma={0,1}` and choose boring-extension families:

- `E_0={constant-zero}`;
- `E_1={first-coordinate projection}`;
- for every `n>=2`, `E_n` is **all** functions `Sigma^n -> Sigma`.

**(B1) holds:** the projection at length 1 is present, and every projection at
length at least 2 belongs to the full function family.

**(B2) holds:** at `m=n=0`, insertion of the constant zero is covered by the
first projection at length 1. All other pairs `m<=n` satisfy `n+1>=2`;
the map `(a,b) -> a e_1(a) b` is injective, so the prescribed outputs
`e_2(ab)` form a consistent partial function, which extends to an element of
the full `E_{n+1}`. There is no need for an unbounded computation.

The map `P(w)=0w` preserves word-tree shapes and lies in `M_E`: it skips only
target level `0`, whose constant-zero witness belongs to `E_0`. For
`Y={00,10}`, direct application of the manuscript's definition gives

```
I_E(Y)    = {0,1,2},    tau_E(Y)    = {00,10};
I_E(P[Y]) = {1,3},      tau_E(P[Y]) = {0,1}.
```

Consequently, **the simultaneous-deletion embedding type is not preserved by
all maps in the monoid under (B1)–(B2)**. This refutes the type-invariance /
reconstruction *step* appealed to in the proof of `thm:boring1`. It does not
prove that the Ramsey conclusion of `thm:boring1` is false. The same issue
propagates to `thm:boring2` when its proof uses that identification. These
applications should remain unvalidated pending a corrected type theorem, an
explicitly verified extra hypothesis (such as a suitable hereditary condition),
or a different envelope-based definition of the type.

`successor_boring_type_validation.py` checks the finite extension families,
the two level-set computations and the type inequality. The unbounded (B2)
argument is as above and is not a claim of exhaustive verification at every
finite size.

A separate **mechanical typo** occurs in the former proof of `thm:boring1`:
the domain of the colouring being pulled back is copies of `X`, not copies of
`Y`, since the very next formula reads `chi(f[tau_E(X)])`. The annotation script
corrects this exact `Y` to `X` only when a unique matching expression occurs.

## Delivery / provenance

The earlier reviewed manuscript archive
`successors-v8-reviewed.tgz` is visible in the Project Library but its raw
bytes could not be mounted in the current container. Hence **this pass did
not directly edit or build that source archive**, and it would be misleading
to call the manuscript patch tested against its exact bytes. Instead the
provided `annotate_successors_v8.py` is a strict, idempotent, label-anchored
patch generator, which can run on either an extracted v8 tree or a v8 `.tgz`
and can emit both the exact unified diff and a patched `.tgz`.

Its functionality has been checked on a clean synthetic TeX tree:
required anchors and annotation insertions, second-pass idempotence,
mechanical `X/Y` correction, `git apply --check` on the generated patch,
and a tar archive extract/annotate/repack cycle. This is an **integration
harness check**, not a claim that the current manuscript compiled.

The next verification work is the boring-extension type/reconstruction claim
and then the individual applications (Milliken, Carlson–Simpson, Graham–Rothschild,
Abramson–Harrington) with explicit statement-level links to their Lean
formalisation. The core Section 5 PR should remain reviewable without merging
unaccepted mathematical prose changes.