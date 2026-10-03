# Adversarial audit: compatible linear extension

Scope: `SuccessorTree/NonPrecompact/LinearExtension.lean`.

This audit targets the circulation lemma `lem:extendlinearmap` from the
BANANA manuscript.  The Lean theorem is slightly more general: the common
codomain is an arbitrary finite-dimensional F₂-space rather than a fixed
coordinate space `F₂^k`.

## Referee A: kernel and quotient decomposition

Let `q,q' : V → W` be surjective and let `f : A ≃ A'` satisfy
`q' (f a) = q a`.  The restrictions of `f` identify
`ker(q|A)` and `ker(q'|A')`.  Since `q` and `q'` are surjective from
the same finite-dimensional space onto the same target, rank-nullity gives
`dim ker q = dim ker q'`.  Therefore the kernel equivalence extends to an
isomorphism `T : ker q ≃ ker q'`.

Choose linear right inverses `s,s'` of `q,q'`.  The kernel coordinates
are
`p(x)=x-s(qx)` and `p'(x)=x-s'(q'x)`.
On `A`, define the discrepancy
`δ(a)=p'(f a)-T(p a)`.
For `a∈ker(q|A)`, both kernel coordinates are the original vectors and
`T` agrees with `f`, so `δ(a)=0`.  Hence `δ` factors through
`q(A)`.  Extending the resulting map `q(A)→ker q'` to all of `W`
produces `L : W→ker q'`.

The final map is
[
  h(x)=T(p(x))+L(qx)+s'(qx).
]
Its `q'`-image is `qx`, and on `A` the definition of `δ` reduces
`h(a)` to `f(a)`.

## Referee B: invertibility

If `h(x)=0`, applying `q'` gives `q(x)=0`.  Thus `p(x)=x`,
`L(qx)=0`, and `s'(qx)=0`, so `T(x)=0`.  Injectivity of `T` gives
`x=0`.  Since `h` is an injective endomorphism of a finite-dimensional
space, it is a linear automorphism.  No cardinality argument or choice of a
basis is hidden here.

For general injectivity, apply this kernel argument to `x-y`.

## Referee C: manuscript comparison and edge cases

The manuscript assumes `W=F₂^k`; the Lean theorem allows any
finite-dimensional `W`.  The case `k=0` is included: both quotient maps
are zero, and the result reduces to extending a subspace equivalence to the
ambient vector space.

Surjectivity is used exactly twice: to identify the dimensions of the two
kernels and to choose linear right inverses.  The partial map need only be a
linear equivalence between subspaces and satisfy the displayed compatibility.

The commented manuscript proof uses bases of the kernels and matching lifts.
The formal proof is the same argument organised canonically through kernels,
quotients and complements; it does not strengthen the assumptions.

## Independent clarity audit

The result should be stated in the paper before perfect-pair homogeneity, as
it already is.  Its proof is currently commented out in the circulation
source.  If Lean verification succeeds, the paper should restore a short
proof; leaving a proved lemma with no visible proof is a circulation
self-containedness defect.

Separately, the current circulation definition saying that `E(x,y)` forms
a matching/perfect matching is incompatible with the later standard perfect
pairings `B_D` for `D>1`.  For instance in `B_2`, `(1,0)` pairs to
one with both `(1,0)` and `(1,1)`.  The intended notion is nondegeneracy:
each nonzero vector pairs nontrivially with some vector on the opposite side,
equivalently either side identifies with the dual of the other.
