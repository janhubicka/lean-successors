# Adversarial audit: finite perfect BANANA homogeneity

Scope: `SuccessorTree/NonPrecompact/PerfectHomogeneity.lean`.

This audit is independent of the implementation pass.  Its target is the
circulation lemma `lem:perfect-homogeneous`: every isomorphism between
finite substructures of a finite perfect pairing extends to an automorphism.

## Referee A: translation of homogeneity

The Lean theorem uses the standard equivalent embedding formulation.
For an arbitrary finite BANANA source `A` and two embeddings
`e₁,e₂ : A → B_n`, it constructs an automorphism `H` of `B_n` with
`H ∘ e₁ = e₂` on both sorts.  An isomorphism between two substructures
of `B_n` is recovered by taking `A` to be its domain, `e₁` the
inclusion and `e₂` the inclusion of the range composed with the given
isomorphism.  Conversely, the displayed conjugacy property is exactly an
extension of that isomorphism.  Thus no rigidity or quotient by
automorphisms of the source is being assumed.

## Referee B: surjectivity of the evaluation maps

For a right embedding
`e.right : F₂^r → F₂^n`, the map `rightPairingMap e : F₂^n → F₂^r`
records all pairings of an ambient left vector with vectors in the embedded
right sort.  Under the standard dot-product identification
`F₂^m ≃ (F₂^m)^*`, this map is the dual of `e.right`.
Since `e.right` is injective, its dual is surjective.  This is precisely
the manuscript's assertion that if `b₁,…,b_k` is a basis of the right
subspace, then
`v ↦ (b₁(v),…,b_k(v))` is onto `F₂^k`.

This point matters: surjectivity is not automatic for an arbitrary list of
functionals; it follows from their linear independence, equivalently from
injectivity of the right embedding.

## Referee C: compatibility on the partial left map

The left ranges of `e₁` and `e₂` are identified through the common
source left sort.  For `z=e₁(x)`, preservation of the BANANA pairing by
both embeddings gives, for every source-right vector `y`,
[
  langle e₂(x),e₂(y)angle
   = eta_A(x,y)
   = langle e₁(x),e₁(y)angle .
]
Therefore the two evaluation maps agree after the partial left
isomorphism.  This is exactly the compatibility hypothesis of
`exists_linearEquiv_extends_of_surjective`.

No use is made of non-degeneracy of the source `A`; only the ambient
target `B_n` is perfect.

## Referee D: the contragredient right action

The extension lemma supplies `h ∈ GL(F₂^n)` with
`q₂ h = q₁` and with `h` extending the left partial isomorphism.
The right action is
[
  k=(h^{-1})^*
]
after identifying the right coordinate space with the dual of the left.
It satisfies
[
  langle h x,k yangle=langle x,yangle
]
for all ambient vectors, so `(h,k)` is an automorphism of the perfect
pairing.

For a source-right vector `y`, the identity `q₂ h=q₁` implies
[
 langle h x,e₂(y)angle
   =langle x,e₁(y)angle
   =langle h x,k(e₁(y))angle
]
for every `x`.  Surjectivity of `h` lets `h x` range over the whole
ambient left space.  Non-degeneracy of the standard dot product therefore
gives `k(e₁(y))=e₂(y)`.  This proves extension on the right sort.

## Referee E: edge cases

The zero-dimensional right source is allowed.  Then the evaluation maps
have zero-dimensional codomain and are trivially surjective; the extension
lemma reduces to extending the left subspace equivalence.  The same argument
handles a zero-dimensional left source.  No step assumes that the source
substructure itself is a perfect pairing.

The ambient dimension `n=0` is also harmless: all spaces and embeddings
are trivial, and the unique automorphism works.

## Manuscript clarity audit

After the correction of the definition of “perfect pairing” from “perfect
matching” to non-degeneracy, the circulation proof has the correct logical
shape.  One sentence can usefully be read as implicit rather than a gap:
the maps
`q(v)=(b_i(v))` and `q'(v)=(b_i'(v))` are surjective because the
`b_i` and `b_i'` are linearly independent functionals.  The formal proof
checks this point explicitly via injectivity of the right embedding and
surjectivity of its dual.

No additional mathematical correction was found in `lem:perfect-homogeneous`.
