# Boring-extension counterexamples and reverse insertion (8 October 2026)

**Scope.** This audits the statements \`thm:boring1\`, \`thm:boring2\`,
\`thm:GR1\`, and \`thm:GR2\` in the supplied successor-tree v8 source.
The statements as printed are false. The repair below is proposed for the
*embedding-type application* and does not change the main SMTree axioms.
It is a mathematical proof note; no new Lean theorem is claimed.

## Two-colour counterexample to B1–B2 embedding-type Ramsey

Take \(\Sigma=\{0,1\}\), \(\mathcal E_0=\{\mathrm{const}\,0\}\),
\(\mathcal E_1=\{a\mapsto a_0\}\) and \(\mathcal E_i\) all functions
\(\Sigma^i\to\Sigma\) for \(i\geq2\).

B1 holds because all projections are present. For B2 with \(m=n=0\), the
first projection at level 1 extends the constant-zero insertion. For
\(n\geq1\), the target family at \(n+1\) contains all functions and the
prescription \(e_3(a\,e_1(a)\,b)=e_2(ab)\) is consistent by injectivity
of \(ab\mapsto a\,e_1(a)\,b\).

Let \(X=\{01\}\), \(Y=\{01,11\}\). Computing interesting levels gives
\(\tau_{\mathcal E}(X)=\{1\}\) and
\(\tau_{\mathcal E}(Y)=\{01,11\}\).
Colour every singleton \(\{w\}\) of type \(\{1\}\) by its first letter.

**Claim.** Every two-word set \(Y'\) with type \(\{01,11\}\) consists of
one word beginning \(01\) and the other beginning \(11\).
The two original word lengths must agree: if one ended earlier, its
endpoint would be an interesting coordinate contributing a letter only to
the longer compressed word, contradicting their equal compressed lengths.
Let \(d\) be their first difference. For every index \(i\geq2\) below the
common endpoint, the full family \(\mathcal E_i\) has a witness exactly
when \(i\ne d\): at \(d\) the same prefix needs different letters; later
the prefixes differ. Since both compressed words have two letters, \(d\)
must be the *first* retained index and there must be a later one. This
excludes \(d\geq1\). Thus \(d=0\); the only second retained index can be 1,
where the common character must be 1. This proves the claim.

Both singleton members of \(Y'\) have type \(\{1\}\), but their first
letters differ. Therefore \(Y'\) is bichromatic. **Both clauses of
\`thm:boring1\` and the cube \`thm:boring2\` are false under B1–B2**,
at every finite height and in the full word tree.

The older, weaker counterexample to invariance is also valid:
\(Z=\{00,10\}\) and \(P(w)=0w\in\mathcal M_{\mathcal E}\) satisfy
\(\tau_{\mathcal E}(Z)=\{00,10\}\) but
\(\tau_{\mathcal E}(P[Z])=\{0,1\}\).

## Sufficient amendment (B3): reverse insertion

For every \(m\leq n\), \(e_1\in\mathcal E_m\) and
\(e_3\in\mathcal E_{n+1}\), demand an \(e_2\in\mathcal E_n\) with

\[
e_2(ab)=e_3(a\,e_1(a)\,b)
\quad(a\in\Sigma^m,\ b\in\Sigma^{n-m}).
\tag{B3}
\]

Write \(J_{m,e}\) for insertion of \(e(w|_m)\) at coordinate \(m\) in
every word of length at least \(m\); write \(\sigma_m(i)=i\) if \(i<m\),
\(\sigma_m(i)=i+1\) otherwise. Under B2+B3, for every finite \(Z\),

\[
I_{\mathcal E}(J_{m,e}[Z])=\sigma_m[I_{\mathcal E}(Z)],
\qquad
\tau_{\mathcal E}(J_{m,e}[Z])=\tau_{\mathcal E}(Z).
\]

**Proof.** Below \(m\), all constraints are unchanged, and at \(m\)
the witness \(e\) works. At \(i>m\), the old constraints at \(i-1\)
match the new constraints at \(i\) via insertion of \(e\).
B2 lifts an old witness and B3 restricts a new witness. Endpoints
shift in the same way.

Every restriction \(F|_{\Sigma^{\leq q}}\) with
\(F\in\mathcal M_{\mathcal E}\) is a product of finitely many
\(J_{j,e_j}\), at the skipped target positions \(j<\widetilde F(q)\)
in increasing order. Passing-number preservation identifies retained
letters; the witness \(e_j\) supplies each skipped letter, after the
previous prefix has been reconstructed. Repeated application proves
\(\tau_{\mathcal E}(F[Z])=\tau_{\mathcal E}(Z)\).

Conversely, for finite \(Z\), select a witness at every noninteresting
coordinate below the maximum endpoint and delete those coordinates
in *decreasing* order. Earlier prefixes have not changed, so their
witnesses remain valid; no word ends at a deleted coordinate.
Deletion is injective: two words with the same preceding prefix
cannot disagree in the deleted coordinate if its witness exists.
Reversing the deletions reconstructs \(Z\) from \(\tau_{\mathcal E}(Z)\)
by allowed one-level insertions. This supplies the type
preservation/reconstruction missing from the paper's Ramsey argument,
assuming B3. The passage to exact-end and empty cases remains to be
checked against the chosen manuscript formulation.

B3 holds for the **maximal**, **projection-only**, and
**projection-plus-\(\Pi\)-constant** families. For projections,
contracting a selected coordinate across an insertion gives the same
old coordinate, the inserted function \(e_1\) (read cylindrically), or
the following coordinate shifted down; a constant remains constant.
For the maximal family just define \(e_2\) by the displayed formula.

The monoid proposition itself needs only B1+B2: closure under
composition is shown by lifting the *current* skipped-position
witness through consecutive outer gaps; a finite insertion normal
form also supplies the last-gap factorization for M2.

## Separate mixed-alphabet Graham–Rothschild obstruction

As written, the two GR theorems allow \(\Pi\subsetneq\Sigma\),
require \(W\) to have constants only in \(\Pi\), but let the
substitution \(U\) use arbitrary constants from \(\Sigma\).
Take \(\Pi=\{0\}\), \(\Sigma=\{0,1\}\), \(k=1,m=2,r=2\).
Colour by whether the literal constant 1 occurs.
For every two-parameter \(W\) over \(\Pi\), the permitted
\(U^0=\lambda_0\lambda_0\) and \(U^1=1\lambda_0\) force opposite
colours. This disproves both the exact and star statements.

Two valid fixes: take \(\Pi=\Sigma\) (usual same-alphabet theorem),
or require the substitution \(U\) to have constants in \(\Pi\).
The projection-plus-constant monoid as defined only controls the latter
substitutions.

## Remaining application checks

- Milliken: follows directly from the maximal strong-embedding monoid.
  Does not require the false general type statement.
- Carlson–Simpson and the dual theorem: B3 holds for projection families,
  but the identification with partitions and the full topological transfer
  still need explicit correspondence checks.
- Graham–Rothschild: B3 holds, but the alphabet correction above is mandatory.
- Abramson–Harrington: verify B3 for its custom family and repair the
  level-structure definition (ordered tuple supports, repetitions and unary
  relations). Check the declared envelope height against the \(k\) passed
  to the cube theorem. These steps are not green-certified.

**Validation evidence.** The finite Python regression on PR #109 tests
B2/B3 in bounded cases, 17,856 one-level type invariance instances for the
three standard families, 1,818 type-\(Y\) target pairs forced bichromatic
for the counterexample family, and 4,414 mixed-alphabet parameter-word
targets. The mathematical arguments above, not those finite counts, cover
all lengths.