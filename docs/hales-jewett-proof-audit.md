# Audit of `Hales-Jewett-by-combinatorial-forcing`

Source audited: `janhubicka/Hales-Jewett-by-combinatorial-forcing/main.tex`
on `main`, with repairs on `proof-audit-fixes` / PR #1 (30 September 2026).

## Target theorem

For the successor-tree pigeonhole argument we need the starred
one-dimensional Hales--Jewett statement:

> for every finite alphabet `Σ` and finite colouring of `Σ^{<ω}`, there is
> a one-variable word `L` such that `L(*)` and every `L(a)` have the
> same colour.

This is Theorem 1.1 of the note (notation `L[Σ^{<2}]`).

## Dependency structure

The forcing proof is an induction on the alphabet size, and this dependency
must be kept explicit.

1. **For a fixed alphabet `Σ`**, assume the finite-colour one-dimensional
   starred theorem for `Σ`.
2. Lemma 1 uses that hypothesis for a finite product colouring.
3. Lemma 2 plus fusion proves Proposition 1: every large set contains all
   finite evaluations of a subspace.
4. Proposition 1 gives the two-colour omega-dimensional theorem.
5. Nested refinement/composition upgrades this to every finite number of
   colours.
6. The omega-dimensional theorem on the smaller alphabet
   `Π = Σ \ {c}` is then used to prove the one-dimensional theorem for
   `Σ`.
7. Induction on `|Σ|` closes the cycle.

Thus Proposition 1 is **not** an unconditional substitute for Hales--Jewett:
its proof uses the same-alphabet one-dimensional theorem. The Lean
formalization records this rather than treating Proposition 1 as an axiom.

## Corrections found in the imported draft

1. **Lemma 1: missing trivial case.** The proof immediately chose a finite
   word avoiding `O`. Such a word need not exist when
   `O = Σ^{<ω}`. The repaired proof handles this case first and otherwise
   starts the maximal-avoider argument from a word outside `O`.

2. **Observation 2: wrong/undefined set in the second case.** If `O₀` is
   not large and `U` avoids `O₀`, every `U(v)` belongs to `O₁`;
   hence the pullback of `O₁` is all of `Σ^{<ω}`, and is large.

3. **Lemma 2: Shift index typo.** For `j<i`, the preserved tail is
   `Shift(Uᶦ, nᵢ-|Lʲ|)(v)`, not `Shift(Uᶦ, nᵢ-|Lᶦ|)(v)`.

4. **Lemma 2: enumeration typo.** `L_j=L` is corrected to `L^j=L`.

5. **Fusion limit step was too terse.** The repair explicitly observes that
   nondecreasing line lengths together with condition (i) stabilize all
   finitely many values in the selected line before passing to the limit.

6. **Empty alphabet base case.** The alphabet induction now includes
   `|Σ|=0`.

7. **Finite-colour gap.** The original text claimed that it was enough to
   prove the one-dimensional theorem for two colours, but Lemma 1 applies it
   to the product colouring
   `χ_v : Σ^n → {0,1}`, which may have many colours. Using a binary
   reduction there would require a refinement/composition argument that was
   not supplied and risks circularity in the presentation.

   The repaired draft proves the finite-colour statement directly in the
   alphabet-size induction. For an `r`-colouring it builds `r+1` nested
   subspaces over the smaller alphabet. Two recorded colours coincide, and
   the corresponding line
   `U(c^{i-1} ⌢ λ₀^{j-i})` is monochromatic.

## Lean checks already completed

The formalization has already verified:

* the concrete block-normal-form variable words;
* the Shift prefix/tail identity;
* subspace composition and `W(U(v)) = W(U)(v)`;
* the combined Shift/substitution identity;
* Observation 1 (largeness survives pullback);
* the corrected Observation 2;
* binary-to-finite-colour refinement by composition.

The next proof obligations are precisely Lemma 1, Lemma 2/fusion,
Proposition 1, and the finite-colour alphabet-increase induction.
