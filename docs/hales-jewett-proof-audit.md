# Audit of `Hales-Jewett-by-combinatorial-forcing`

Source audited: `janhubicka/Hales-Jewett-by-combinatorial-forcing/main.tex` on `main`, together with the repairs on branch `proof-audit-fixes` / PR #1 (2026-09-30).

## Target theorem

For the successor-tree pigeonhole argument we need the infinite starred
one-dimensional Hales--Jewett statement:

> for every finite alphabet `Σ` and finite colouring of `Σ^{<ω}`, there is a
> one-variable word `L` such that the prefix `L(*)` and every evaluation `L(a)`
> have the same colour.

This is exactly Theorem 1.1 of the note (its notation `L[Σ^{<2}]`).  The
successor-tree proof can use this infinite form directly; a separate compactness
argument to a bounded finite Hales--Jewett number is only needed later for a
fully finite theorem.

## Audit result

The combinatorial-forcing proof is structurally coherent.  The dependency
cycle is:

1. one-dimensional starred HJ for an alphabet `Σ` implies the omega-dimensional
   starred theorem for `Σ`;
2. the omega-dimensional theorem for smaller alphabets is used to increase the
   alphabet size and prove one-dimensional starred HJ for `Σ`;
3. induction on `|Σ|` closes the argument.

The forcing section uses the usual large-set fusion: Lemma 1 obtains a line in
any large set; Lemma 2 produces one stable first coordinate while preserving
largeness in the tail; Proposition 1 iterates Lemma 2 and takes a fusion limit.
No finite Hales--Jewett theorem is used as a black box.

## Corrections found

These are local repairs, not changes to the proof strategy.

1. **Lemma 1: trivial large set case.**  The proof begins by choosing a finite
   variable word avoiding `O`.  Such a word need not exist when
   `O = Σ^{<ω}`.  Split this case off first (then every line works).  Otherwise
   choose a word outside `O` as a 0-variable avoider and run the stated maximal
   extension argument.

2. **Observation 2: undefined `O`.**  In the second case, if `O₀` is not large
   and `U` avoids `O₀`, then every `U(v)` lies in `O₁`; hence
   `{v : U(v) ∈ O₁} = Σ^{<ω}`, which is large.  The displayed reference to an
   undefined `O` should be replaced by this sentence.

3. **Lemma 2: shifted-tail index typo.**  In the preservation of condition (ii)
   for `j < i`, the relevant word is
   `Shift(Uᶦ, nᵢ - |Lʲ|)(v)`.  One subsequent occurrence currently reads
   `nᵢ - |Lᶦ|`.

4. **Lemma 2: enumeration typo.**  Near the final contradiction, `L_j = L`
   should read `L^j = L`.

5. **Alphabet induction: empty alphabet.**  The original induction started with
   `|Σ| = 1`.  Since the theorem is stated for every finite alphabet, add the
   trivial `|Σ| = 0` case.  This is already repaired on `proof-audit-fixes`.

All five repairs are present in PR #1.  I found no change to the proof strategy after these local corrections; the remaining proof obligations are the substitution/fusion identities below, which are exactly the parts Lean should make explicit.

## Points to make explicit in Lean

The paper uses several substitution identities as "easy to see" steps.  The
formalization should isolate them before tackling largeness:

* associativity of substitution: `W(U(v)) = W(U)(v)`;
* prefix/tail identity for `Shift`;
* the variable-word version of the shift identity (the text states the constant
  prefix instance but later applies it to a line prefix);
* stabilization of fusion limits under the conditions fixing longer and longer
  initial variable blocks;
* finiteness of the set of lines of bounded length, used to enumerate all lines
  in nondecreasing length with lengths tending to infinity.

The alphabet-increase argument then only needs the pigeonhole fact that among
three 2-colours two agree, plus explicit substitution calculations for the
three candidate lines.

## Lean plan

`SuccessorTree.Support.StarHJ` currently states exactly the infinite
one-dimensional starred theorem above.  We first formalize the variable-word
calculus and the forcing proof from this note to discharge `StarHJ`.  Only then
will the successor-tree-specific M1--M3/replay layer be developed.
