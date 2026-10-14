import SuccessorTree.V10.I3PrescribedOriginalWitness
import SuccessorTree.V10.PartialTypeRestriction
import Mathlib.Tactic

/-!
# A concrete prescribed B1/B2 source from one finite ambient original pool

In the author's I3 construction a finite set of named original vertices
of a fixed partial structure C supplies old level-ell source types and
their prescribed level-(ell+1) crossing types. This module constructs
one genuinely well-defined partial function on those source types:
when several named originals have the same old type, choose ONE of
them to define the output. The remaining upper type vertices may
differ, but B2 sees only the common ordinary L+ socle of C.

Unlike a mere assumed PrescribedBoringData, both B1 and B2 are proved
here, and every output carries a specific original-name witness.
Consequently a failure of the author's corrected B3 produces a
finite L-only witness with those named upper originals, by the
verified I3PrescribedOriginalWitness interface.

The separate manuscript proof must still show that the actual I3
function f_ell is this ambient-pool prescription, or has an equivalent
source/output representation. No statement about axiom weakening or
arbitrary relation arities is made.
-/

namespace SuccessorTree.V10

/-- Complete ordinary L+ socles of two actual types extracted at
the same cut from one ambient partial structure are literally equal.
This includes every E pair, unary and diagonal atom. -/
theorem sameOrdinarySocle_ambient_types
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell u v : Nat) :
    SameOrdinarySocle
      (A.partialTypeAt (ell + 1) u)
      (A.partialTypeAt (ell + 1) v) := by
  exact ⟨by intros; rfl, by intros; rfl,
    by intros; rfl, by intros; rfl⟩

/-- The full L-reduct of an extracted actual ambient type is
definitionally its induced type over the same finite initial cut. -/
theorem partialTypeAt_lReduct_eq_ofAgeModel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (cut v : Nat) :
    (A.partialTypeAt cut v).lReduct =
      RelationalPrefixType.ofAgeModel A.L cut v := rfl

/-- The actual finite-pool B1/B2 prescription. Domain membership is
literal equality with an old ambient source type. The arbitrary
output outside the source is used only to make the record total;
no B1/B2 assertion depends on that dummy value.

Non-unique representatives are resolved by choosing a matching
original; this is harmless because their old types agree and their
new ordinary socles agree within the same ambient A. -/
noncomputable def ambientPoolPrescribedData
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat) :
    PrescribedBoringData ell db du dd where
  source := Set.range (fun v : Fin M => A.partialTypeAt ell (original v))
  target := fun T =>
    if h : ∃ v : Fin M, A.partialTypeAt ell (original v) = T then
      A.partialTypeAt (ell+1) (original (Classical.choose h))
    else A.partialTypeAt (ell+1) 0
  extendsSource := by
    intro T hT
    change ∃ v : Fin M, A.partialTypeAt ell (original v) = T at hT
    change
      (if h : ∃ v : Fin M, A.partialTypeAt ell (original v) = T then
        A.partialTypeAt (ell+1) (original (Classical.choose h))
       else A.partialTypeAt (ell+1) 0).restrict (Nat.le_succ ell) = T
    rw [dif_pos hT]
    exact (A.partialTypeAt_restrict ell (ell+1)
      (original (Classical.choose hT)) (Nat.le_succ ell)).trans
        (Classical.choose_spec hT)
  preservesCompatibility := by
    intro T U hT hU _hComp
    change ∃ v : Fin M, A.partialTypeAt ell (original v) = T at hT
    change ∃ v : Fin M, A.partialTypeAt ell (original v) = U at hU
    change SameOrdinarySocle
      (if h : ∃ v : Fin M, A.partialTypeAt ell (original v) = T then
        A.partialTypeAt (ell+1) (original (Classical.choose h))
       else A.partialTypeAt (ell+1) 0)
      (if h : ∃ v : Fin M, A.partialTypeAt ell (original v) = U then
        A.partialTypeAt (ell+1) (original (Classical.choose h))
       else A.partialTypeAt (ell+1) 0)
    rw [dif_pos hT, dif_pos hU]
    exact sameOrdinarySocle_ambient_types A ell
      (original (Classical.choose hT))
      (original (Classical.choose hU))

/-- A concrete source/target type pair in the actual pool always has
one SAME original vertex witnessing both old and new records. The
new L-type includes positive and negative facts at the inserted cut. -/
theorem ambientPoolPrescribedData_source_original
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (ambientPoolPrescribedData A ell original).source) :
    ∃ v : Fin M,
      T = A.partialTypeAt ell (original v) ∧
      ((ambientPoolPrescribedData A ell original).target T).lReduct =
        RelationalPrefixType.ofAgeModel A.L (ell+1) (original v) := by
  classical
  change ∃ v : Fin M, A.partialTypeAt ell (original v) = T at hT
  let v : Fin M := Classical.choose hT
  have hv : A.partialTypeAt ell (original v) = T :=
    Classical.choose_spec hT
  refine ⟨v,hv.symm,?_⟩
  change
    (if h : ∃ w : Fin M, A.partialTypeAt ell (original w) = T then
      A.partialTypeAt (ell+1) (original (Classical.choose h))
     else A.partialTypeAt (ell+1) 0).lReduct =
       RelationalPrefixType.ofAgeModel A.L (ell+1) (original v)
  rw [dif_pos hT]
  exact partialTypeAt_lReduct_eq_ofAgeModel A (ell+1) (original v)

/-- The actual ambient-pool construction and a failed manuscript B3
test already yield the finite L-only witness with named originals.
The hypothesis is ONLY the failure of corrected B3 on the
constructed B1/B2 partial function. -/
theorem ambientPool_failedCorrectedB3_has_original_witness
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (hFailure :
      ¬ (ambientPoolPrescribedData A ell original).CorrectedB3 family) :
    ∃ S0 : PartialTypeWithE ell db du dd,
      S0 ∈ (ambientPoolPrescribedData A ell original).source ∧
      ∃ W : AgeTestModel db du dd,
        W.BoundedCarrier ∧
        SameInitialL W
          (prescribedOrdinarySocle
            ((ambientPoolPrescribedData A ell original).target S0)) ell ∧
        (∀ bad, bad ∈ family → bad.Avoids (W.withoutVertex ell)) ∧
        (∀ x, x ∈ W.carrier → ell < x →
          ∃ v : Fin M,
            RelationalPrefixType.ofAgeModel W (ell+1) x =
              RelationalPrefixType.ofAgeModel A.L (ell+1) (original v)) ∧
        ∃ bad, bad ∈ family ∧ ¬ bad.Avoids W := by
  exact (ambientPoolPrescribedData A ell original).
    failedCorrectedB3_of_actual_original_pool
      family A original
      (ambientPoolPrescribedData_source_original A ell original)
      hFailure

end SuccessorTree.V10
