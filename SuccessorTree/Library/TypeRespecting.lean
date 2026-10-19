import SuccessorTree.V10.TypeRespectingRamsey
import SuccessorTree.V10.FiniteTypeProfileFullType

/-!
# Public binary type-respecting Ramsey theorem

This narrow import exposes the finite full profiles, their intrinsic
continuation condition, complete retained-record and free-level transport,
the finite extension theorem, and the resulting degree-one Ramsey theorem.

The main endpoint is `SuccessorTree.V10.normalizedKpt_typeRespectingRamsey`.
Its coloured objects are `TypeRespectingEmbedding A`, identified by their
actual finite functions. `TypeRespectingEmbedding.act` is literal
postcomposition by the returned normalized Kpt monoid map.

The normalized finite unary/directed-binary/diagonal language and auxiliary
E relation are part of the public assumptions. No global extendibility is
included in the intrinsic definition; `FiniteTypeProfileMap.extends` proves
it using the existing compatible boring extension and canonical gap closing.
-/
