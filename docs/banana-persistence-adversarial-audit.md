# Adversarial audit: BANANA affine-slice persistence

This audit concerns `SuccessorTree/NonPrecompact/BananaPersistence.lean`.
It is intentionally separate from the proof script and checks the new
formalisation from two different directions.

## Referee A — dimensions, transposes, and algebra

**Target.** Check that the Lean matrices encode exactly the matrix argument in
the BANANA persistence proof and that no row/column convention was reversed.

The manuscript uses coordinate matrices `P,Q : N × q` with
`Pᵀ Q = I_q`.  The Lean residue library uses their transposes:
`A,B : q × N`, hence the hypothesis is `A Bᵀ = I_q`.
For `q=d+1`, `frontRows` is the submatrix obtained by the inclusion
`Fin d -> Fin (d+1)`.  Therefore
`
frontRows A * (frontRows B)ᵀ
`
is precisely the upper-left `d × d` principal submatrix of `A Bᵀ`.
The theorem `frontRows_mul_transpose_eq_one` proves this using
`Matrix.submatrix_mul` and `Matrix.submatrix_one`; no rank argument or
unstated choice of coordinates is used.

On the last-coordinate-one slice, a column functional decomposes as
`
a_i · (u,1) = a_i^{front} · u + a_i^{last}.
`
The theorem `affineBit_frontRows_lastOffset` proves this identity
coordinatewise, and `bilinearWeight_frontRows_lastOffset` sums it as an
equality of ordinary natural-number weights.  Thus the affine residue theorem
is applied to exactly the same integer intersection count as in the original
full pair.

Finally, `natCast_bilinearWeight_eq_dotProduct` checks the parity identity.
After casting the ordinary count to `F₂`, the sum is
`
(Aᵀ x) · (Bᵀ y) = (x A) · (Bᵀ y)
                 = (x (A Bᵀ)) · y
                 = x · y.
`
This uses only `A Bᵀ = I`.

**Verdict.** The matrix orientation, deleted-coordinate reduction, and parity
identity are consistent with the manuscript.

## Referee B — adversarial edge cases and witness semantics

I looked for ways in which the affine residue theorem could return witnesses
that do not correspond to the intended BANANA line pairs.

* **Zero witnesses.**  `snocOne u` has last coordinate one, so it is nonzero
  even when `u=0`.  The same holds on the right.  This is formalised by
  `snocOne_ne_zero`.
* **Singular truncated system.**  This cannot occur: the truncated product is
  literally the upper-left block of the identity, formalised by
  `frontRows_mul_transpose_eq_one`.
* **Too few ambient coordinates.**  No separate inequality `n >= q` is
  assumed.  It is unnecessary: the left-inverse equation itself forces the
  required rank.  The residue theorem only consumes that equation.
* **Affine offsets.**  The offsets are exactly the deleted last rows of the
  two matrices, with no extra compatibility assumptions.  The affine residue
  theorem was deliberately formalised for arbitrary offsets.
* **Wrong parity class.**  The combined theorem
  `exists_nonzero_full_bilinearWeight_eq_residue_with_pairing` packages the
  residue witness together with
  `x · y = cast(r) : F₂`, so a residue cannot be assigned to the wrong
  one-atom pairing type.
* **Smallest case.**  The argument includes `k=0` (`q=2,d=1`); no proof
  step requires `k>0`.

As an independent finite check, all perfect pairs were enumerated for
`2 × 2` (6 pairs) and `2 × 3` (168 pairs), and 300 random perfect pairs
were tested in dimension 4.  In every case the affine/full weight identity
and the parity identity held, and every required residue was realised.

**Verdict.** No counterexample was found; the nonzero and parity conditions
needed for the two rigid four-element BANANA sources are explicitly present
in the formal statement.

## Remaining interface boundary

This file deliberately stops at the matrix presentation.  It does **not** yet
formalise the Fraïssé-language notions of a BANANA structure, an embedding, a
copy of `B_q`, or a copy of the rigid line pair `A_b`.  Consequently the
manuscript theorem about copy Ramsey degrees should still be marked as only
partially Lean-verified until that structural interface is formalised.  The
new file verifies the complete linear-algebra/residue core of its second
case.
