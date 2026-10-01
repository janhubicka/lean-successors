import SuccessorTree.BANANA.TupleInvariant

namespace SuccessorTree.BANANA

open scoped BigOperators

/-- Equality of the pairings on the distinguished generators extends to
all linear combinations of those generators. -/
theorem pairing_tupleLinearMap_eq
    {L R L' R' : Type*}
    [AddCommGroup L] [Module F2 L]
    [AddCommGroup R] [Module F2 R]
    [AddCommGroup L'] [Module F2 L']
    [AddCommGroup R'] [Module F2 R']
    {m n : ℕ}
    (β : L →ₗ[F2] R →ₗ[F2] F2)
    (β' : L' →ₗ[F2] R' →ₗ[F2] F2)
    (x : Fin m → L) (x' : Fin m → L')
    (y : Fin n → R) (y' : Fin n → R')
    (hpair : ∀ i j, β (x i) (y j) = β' (x' i) (y' j))
    (c : Fin m → F2) (d : Fin n → F2) :
    β (tupleLinearMap x c) (tupleLinearMap y d) =
      β' (tupleLinearMap x' c) (tupleLinearMap y' d) := by
  simp only [tupleLinearMap_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  simp_rw [hpair]

/-- Equal tuple invariants induce an isomorphism of the generated
two-sorted bilinear substructures.  The two returned linear equivalences
are the canonical first-isomorphism-theorem identifications of the
generated spans. -/
theorem tupleInvariant_eq_induces_generated_pairing_equiv
    {L R L' R' : Type*}
    [AddCommGroup L] [Module F2 L] [DecidableEq L]
    [AddCommGroup R] [Module F2 R] [DecidableEq R]
    [AddCommGroup L'] [Module F2 L'] [DecidableEq L']
    [AddCommGroup R'] [Module F2 R'] [DecidableEq R']
    {m n : ℕ}
    (β : L →ₗ[F2] R →ₗ[F2] F2)
    (β' : L' →ₗ[F2] R' →ₗ[F2] F2)
    (x : Fin m → L) (x' : Fin m → L')
    (y : Fin n → R) (y' : Fin n → R')
    (h :
      tupleInvariant (fun a b => β a b) x y =
        tupleInvariant (fun a b => β' a b) x' y') :
    let eL :=
      generatedSpanEquivOfRelationPatternEq x x'
        (by
          have hL := congrArg TupleInvariant.leftRelations h
          change relationPattern x = relationPattern x' at hL
          exact hL)
    let eR :=
      generatedSpanEquivOfRelationPatternEq y y'
        (by
          have hR := congrArg TupleInvariant.rightRelations h
          change relationPattern y = relationPattern y' at hR
          exact hR)
    (∀ i,
        eL ⟨x i, tuple_mem_generated_range x i⟩ =
          ⟨x' i, tuple_mem_generated_range x' i⟩) ∧
      (∀ j,
        eR ⟨y j, tuple_mem_generated_range y j⟩ =
          ⟨y' j, tuple_mem_generated_range y' j⟩) ∧
      ∀ u v, β (u : L) (v : R) = β' (eL u : L') (eR v : R') := by
  have hL := congrArg TupleInvariant.leftRelations h
  change relationPattern x = relationPattern x' at hL
  have hR := congrArg TupleInvariant.rightRelations h
  change relationPattern y = relationPattern y' at hR
  have hp := congrArg TupleInvariant.pairing h
  change (fun i j => β (x i) (y j)) = (fun i j => β' (x' i) (y' j)) at hp
  let eL := generatedSpanEquivOfRelationPatternEq x x' hL
  let eR := generatedSpanEquivOfRelationPatternEq y y' hR
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact generatedSpanEquivOfRelationPatternEq_apply_generator x x' hL i
  · intro j
    exact generatedSpanEquivOfRelationPatternEq_apply_generator y y' hR j
  · rintro ⟨_, ⟨c, rfl⟩⟩ ⟨_, ⟨d, rfl⟩⟩
    rw [generatedSpanEquivOfRelationPatternEq_apply_tupleLinearMap x x' hL c,
      generatedSpanEquivOfRelationPatternEq_apply_tupleLinearMap y y' hR d]
    apply pairing_tupleLinearMap_eq β β' x x' y y'
    intro i j
    exact congrFun (congrFun hp i) j

end SuccessorTree.BANANA
