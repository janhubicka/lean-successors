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
all maps in the monoid under (B1)–(B2)**. More strongly, both general Ramsey
theorems are **false under those hypotheses**. Take X={01} and Y={01,11}.
Then tau(X)={1} and tau(Y)={01,11}. Colour singleton copies of type {1}
by their first letter. Every Y' of type {01,11} consists of one word
beginning 01 and one beginning 11, both singleton members having type {1}.
Thus every Y' contains both colours, at every length (and in the infinite
tree). This refutes both clauses of thm:boring1 and the cube thm:boring2.

A sufficient application-level repair is the **reverse insertion axiom**
(B3): for all m<=n, e1 in E_m and e3 in E_{n+1}, there exists e2 in E_n
such that e2(a b)=e3(a e1(a) b) for all words a,b of lengths m,n-m.
Under B2+B3, the interesting levels after inserting a boring coordinate
are precisely the old interesting levels shifted past that coordinate.
Consequently the finite type tau is invariant under every map in M_E,
by the finite insertion normal form. All three standard families
(maximal functions, projections only, projections plus constants) satisfy
B3. This is a proposed amendment to the **embedding-type applications**,
not a new assumption on the successor-tree theorem itself.

Separately, both Graham–Rothschild formulations thm:GR1 and thm:GR2
are false for proper Pi subsetneq Sigma: with Pi={0}, Sigma={0,1},
k=1, m=2, colour a one-parameter word by whether the literal constant
1 occurs. The allowed substitutions U=lambda0 lambda0 and U=1 lambda0
force opposite colours for any two-parameter W with constants from Pi.
The correction is to take Pi=Sigma, or to restrict the substitution U
to constants in Pi. The manuscript proof actually handles the latter.

These are **mathematical counterexamples**, not only missing formal steps.
The standalone note supplies proofs and a conditional repair; the finite
scripts provide independent bounded diagnostics. No newly proposed
conditional theorem is claimed Lean-certified.

`successor_boring_type_validation.py` checks the finite extension families,
the two level-set computations and the type inequality. The unbounded (B2)
argument is as above and is not a claim of exhaustive verification at every
finite size.

A separate **mechanical typo** occurs in the former proof of `thm:boring1`:
the domain of the colouring being pulled back is copies of `X`, not copies of
`Y`, since the very next formula reads `chi(f[tau_E(X)])`. The annotation script
corrects this exact `Y` to `X` only when a unique matching expression occurs.

## Delivery / provenance (updated after exact upload)

The user supplied the exact manuscript archive successors-v8(1).tgz.
Its content hash matches the previous v8 checkpoint
b104586c62ff4a3a859950965107d2fa2af4d9a66ebd7a0f6f3fd03c5e5c4c95;
the embedded Git revision is b36a2772093c783cd03760edeb49f4e35b655db4.
The Section 5 validation and TODO patch was applied to those source
bytes and independently rebuilt with pdfLaTeX/BibTeX (39 pages).
The subsequent Section 6 counterexample review updates the same tree:
four red counterexample markers, proposed B3, corrected AH indices,
and explicit TODOs. A fresh LaTeX/BibTeX build of this second stage
completed (40 pages, no undefined citations/references). These source
artifacts and the four-page standalone mathematical review note are
produced in the conversation, not stored in this Lean repository.

The manuscript is not silently converted to the proposed conditional
B3 theorem; the new theorem requires editorial approval and kernel
verification. PR #107 still contains the separately checked envelope
formalisation. The full manuscript's applications are not all certified.
