import SuccessorTree.V10.I3AmbientPrescribedPool
import SuccessorTree.V10.I3PrescribedOriginalWitness
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# I3: finite stage original pools with cut-dependent eligible sources

The fixed finite original pool used to count signatures may contain
vertices whose free E-level does not reach a particular tested cut ell.
The source of that level's prescribed B1/B2 map consists ONLY of the
eligible originals with freeLevel(original) >= ell+1.

The definitions below use one fixed list of original addresses and
a cut-dependent eligibility predicate. Equal old partial types are
deduplicated by a classical choice of a representative; its complete
target prefix comes from the SAME representative. All targets of
actual sources are admissible Kpt types because each eligible
original lies in the forbidden-free ambient partial structure and
has the required free cut.

In particular the signatures remain valued in the SAME original
pool, of cardinal at most M, despite different eligible subsets at
different levels. No E is imposed on a finite B3 L-age witness.
The manuscript's exact I3 stage/source algorithm must still be
identified with this filtered prescription before calling the
final big-Ramsey bound complete.
-/

namespace SuccessorTree.V10

/-- A total target on all level-ell types, using the next-cut type
of an eligible original representing that source. When no such
original exists, choose an arbitrary default; B1/B2 never refer to
that value. -/
noncomputable def eligibleAmbientPoolTarget
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (Eligible : Fin M → Prop)
    (T : PartialTypeWithE ell db du dd) :
    PartialTypeWithE (ell+1) db du dd := by
  classical
  exact if h : ∃ v : Fin M,
      Eligible v ∧ A.partialTypeAt ell (original v) = T then
    A.partialTypeAt (ell+1) (original (Classical.choose h))
  else A.partialTypeAt (ell+1) 0

/-- The genuine B1/B2 partial function on the eligible portion of
a fixed ambient-original pool. The complete ordinary L+ socle of
the target is independent of which original represents a source. -/
noncomputable def eligibleAmbientPoolPrescribedData
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (Eligible : Fin M → Prop) :
    PrescribedBoringData ell db du dd where
  source := {T | ∃ v : Fin M,
    Eligible v ∧ A.partialTypeAt ell (original v) = T}
  target := eligibleAmbientPoolTarget A ell original Eligible
  extendsSource := by
    classical
    intro T hT
    change ∃ v : Fin M,
      Eligible v ∧ A.partialTypeAt ell (original v) = T at hT
    change (eligibleAmbientPoolTarget A ell original Eligible T).restrict
      (Nat.le_succ ell) = T
    simp only [eligibleAmbientPoolTarget, dite_eq_left hT]
    exact (A.partialTypeAt_restrict ell (ell+1)
      (original (Classical.choose hT)) (Nat.le_succ ell)).trans
      (Classical.choose_spec hT).2
  preservesCompatibility := by
    classical
    intro T U hT hU _hComp
    change ∃ v : Fin M,
      Eligible v ∧ A.partialTypeAt ell (original v) = T at hT
    change ∃ v : Fin M,
      Eligible v ∧ A.partialTypeAt ell (original v) = U at hU
    change SameOrdinarySocle
      (eligibleAmbientPoolTarget A ell original Eligible T)
      (eligibleAmbientPoolTarget A ell original Eligible U)
    simp only [eligibleAmbientPoolTarget,
      dite_eq_left hT, dite_eq_left hU]
    exact sameOrdinarySocle_ambient_types A ell
      (original (Classical.choose hT))
      (original (Classical.choose hU))

/-- The eligible original represented by an actual source yields
BOTH its old full L+ type and its new full L+ target record. -/
theorem eligibleAmbientPoolPrescribedData_source_original
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Nat)
    (Eligible : Fin M → Prop)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (eligibleAmbientPoolPrescribedData
      A ell original Eligible).source) :
    ∃ v : Fin M,
      Eligible v ∧
      T = A.partialTypeAt ell (original v) ∧
      (eligibleAmbientPoolPrescribedData
        A ell original Eligible).target T =
        A.partialTypeAt (ell+1) (original v) := by
  classical
  change ∃ v : Fin M,
    Eligible v ∧ A.partialTypeAt ell (original v) = T at hT
  let v : Fin M := Classical.choose hT
  obtain ⟨hEligible,hType⟩ := Classical.choose_spec hT
  refine ⟨v,hEligible,hType.symm,?_⟩
  change eligibleAmbientPoolTarget A ell original Eligible T =
    A.partialTypeAt (ell+1) (original v)
  simp only [eligibleAmbientPoolTarget, dite_eq_left hT]
  rfl

/-- The finite stage pool consists of actual ambient vertices.
Eligibility at ell means the original's real free E-cut reaches
the next coordinate ell+1, so its crossing at this level is
genuinely represented in the Kpt tree. -/
noncomputable def stagePoolPrescribedData
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat)
    (original : Fin M → Fin A.size) :
    PrescribedBoringData ell db du dd :=
  eligibleAmbientPoolPrescribedData A ell
    (fun v => (original v).val)
    (fun v => ell+1 ≤ A.freeLevel (original v).val)

/-- Every source of the filtered stage map still has a single
ambient original name in the fixed pool, with free cut reaching
ell+1. It carries both complete source and target type records,
not merely a positive-atom crossing mask. -/
theorem stagePoolPrescribedData_source_original
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size)
    (T : PartialTypeWithE ell db du dd)
    (hT : T ∈ (stagePoolPrescribedData A ell original).source) :
    ∃ v : Fin M,
      ell+1 ≤ A.freeLevel (original v).val ∧
      T = A.partialTypeAt ell (original v).val ∧
      (stagePoolPrescribedData A ell original).target T =
        A.partialTypeAt (ell+1) (original v).val := by
  exact eligibleAmbientPoolPrescribedData_source_original
    A ell (fun v => (original v).val)
    (fun v => ell+1 ≤ A.freeLevel (original v).val)
    T hT

/-- The cut-filtered pool has the exact original-name
representation needed by the manuscript's finite I3 age-signature
witness lemma, while keeping the original-name set of size M fixed
across different tested levels.

The source and its output both come from one eligible original, so
the full L-reduct through ell+1 agrees, including absent tuples. -/
theorem stagePoolPrescribedData_has_original_pool_representation
    {db du dd M : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size) :
    ∀ T, T ∈ (stagePoolPrescribedData A ell original).source →
      ∃ v : Fin M,
        T = A.partialTypeAt ell (original v).val ∧
        ((stagePoolPrescribedData A ell original).target T).lReduct =
          RelationalPrefixType.ofAgeModel A.L (ell+1)
            (original v).val := by
  intro T hT
  obtain ⟨v,_hCut,hOld,hTarget⟩ :=
    stagePoolPrescribedData_source_original A ell original T hT
  refine ⟨v,hOld,?_⟩
  rw [hTarget]
  exact partialTypeAt_lReduct_eq_ofAgeModel A (ell+1)
    (original v).val

/-- Every actual stage target satisfies the admissible Kpt
predicate, with the membership and free-cut witnesses extracted
from its SAME named original in the fixed pool. -/
theorem stagePoolPrescribedData_targets_admissible
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (ell : Nat) (original : Fin M → Fin A.size) :
    ∀ T, T ∈ (stagePoolPrescribedData A ell original).source →
      IsAdmissibleRawType family
        (⟨ell+1,(stagePoolPrescribedData A ell original).target T⟩ :
          RawPartialTypeNode db du dd) := by
  intro T hT
  obtain ⟨v,hCut,_hOld,hTarget⟩ :=
    stagePoolPrescribedData_source_original A ell original T hT
  rw [hTarget]
  have hOldAd : IsAdmissibleRawType family
      (A.rawTypeAtFree (original v).val) :=
    ⟨A,(original v).val,(original v).isLt,hAvoidA,rfl⟩
  have hPrefix :=
    admissibleRawType_closed_under_prefix
      family hOldAd (ell+1) hCut
  change IsAdmissibleRawType family
    (⟨ell+1,
      (A.partialTypeAt (A.freeLevel (original v).val)
        (original v).val).restrict hCut⟩ :
      RawPartialTypeNode db du dd) at hPrefix
  rw [A.partialTypeAt_restrict
    (ell+1) (A.freeLevel (original v).val) (original v).val hCut]
    at hPrefix
  exact hPrefix

/-- The filtered source of a fixed ambient pool belongs to one
ordinary L+ socle. Thus the original corrected B3 is equivalent
to the compatible-class B3 used by the insertion construction. -/
theorem stagePoolPrescribedData_correctedB3_iff_compatibleB3
    {db du dd M : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) (original : Fin M → Fin A.size) :
    (stagePoolPrescribedData A ell original).CorrectedB3 family ↔
      (stagePoolPrescribedData A ell original).CompatibleB3 family := by
  let F := stagePoolPrescribedData A ell original
  have hSource : ∀ T, T ∈ F.source →
      ∃ u : Nat, T = A.partialTypeAt ell u := by
    intro T hT
    obtain ⟨v,_hCut,hOld,_hTarget⟩ :=
      stagePoolPrescribedData_source_original A ell original T hT
    exact ⟨(original v).val,hOld⟩
  have hPairwise : ∀ T U, T ∈ F.source → U ∈ F.source →
      SameOrdinaryAtCut T U :=
    F.source_pairwise_compatible_of_ambient A hSource
  exact F.correctedB3_iff_compatibleB3_of_one_socle family hPairwise

end SuccessorTree.V10
