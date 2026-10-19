import SuccessorTree.FiniteRestrictionRamsey
import SuccessorTree.V10.FiniteTypeProfileExtension
import SuccessorTree.V10.FiniteTypeProfileRestriction
import SuccessorTree.V10.FiniteTypeProfileAction
import SuccessorTree.V10.FiniteTypeProfileAgeEquivalence
import SuccessorTree.V10.FiniteTypeProfileFullType

/-!
# Binary Ramsey theorem for intrinsic type-respecting approximations

The coloured objects are the intrinsic finite full-profile maps defined in
`FiniteTypeProfile`. Their identification with actual restrictions of monoid
maps is proved in both directions. The Ramsey conclusion then follows from
the same finite-dimensional theorem used by the finite BRD construction.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FiniteTypeProfileMap

/-- Every global normalized Kpt map gives an intrinsic finite type-respecting
map on every admissible finite source base. -/
noncomputable def ofShapeMap (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family) : FiniteTypeProfileMap A (A.shapeImage F) where
  toCoherentTypeProfileMap := CoherentTypeProfileMap.ofShapeMap A F hF
  age := (CoherentTypeProfileMap.ofShapeMap A F hF).preservesAge_of_shapeMap_restriction
    F (fun _ => rfl)

@[simp] theorem ofShapeMap_apply (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family) (u : TypeProfile A) :
    ofShapeMap A F hF u = F u.1 := rfl

end FiniteTypeProfileMap

namespace TypeRespectingEmbedding

variable (A : FiniteTypeBase family)

/-- Intrinsic finite maps extend globally; the extension is a conclusion. -/
theorem exists_extension (f : TypeRespectingEmbedding A) :
    ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
      ∀ u : TypeProfile A, F u.1 = f.1 u := by
  obtain ⟨B, h, hf⟩ := f.2
  obtain ⟨F, hFM, hF⟩ := h.extends
  refine ⟨⟨F, hFM⟩, ?_⟩
  intro u
  rw [hf]
  exact hF u

/-- Forget only the finite certificate, keeping the exact coloured function. -/
def toRestriction (f : TypeRespectingEmbedding A) :
    SuccessorTree.SMTree.Restriction (normalizedKptSMTree family)
      (fun u : TypeProfile A => u.1) := by
  refine ⟨f.1, ?_⟩
  obtain ⟨F, hF⟩ := exists_extension A f
  exact ⟨F, funext (fun u => (hF u).symm)⟩

/-- Every actual monoid restriction satisfies the intrinsic finite clauses. -/
noncomputable def ofRestriction
    (f : SuccessorTree.SMTree.Restriction (normalizedKptSMTree family)
      (fun u : TypeProfile A => u.1)) : TypeRespectingEmbedding A := by
  refine ⟨f.1, ?_⟩
  obtain ⟨F, hF⟩ := f.2
  exact ⟨A.shapeImage F.map, FiniteTypeProfileMap.ofShapeMap A F.map F.mem, hF⟩

/-- Equality of intrinsic approximations and restrictions, as an equivalence
which is literally the identity on their underlying finite functions. -/
noncomputable def restrictionEquiv : TypeRespectingEmbedding A ≃
    SuccessorTree.SMTree.Restriction (normalizedKptSMTree family)
      (fun u : TypeProfile A => u.1) where
  toFun := toRestriction A
  invFun := ofRestriction A
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl

/-- Literal postcomposition of an intrinsic approximation by a global map. -/
noncomputable def act
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (f : TypeRespectingEmbedding A) : TypeRespectingEmbedding A :=
  ofRestriction A (SuccessorTree.SMTree.Restriction.act
    (normalizedKptSMTree family) (fun u : TypeProfile A => u.1)
      F (toRestriction A f))

@[simp] theorem act_apply
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (f : TypeRespectingEmbedding A) (u : TypeProfile A) :
    (act A F f).1 u = F (f.1 u) := rfl

@[simp] theorem act_id (f : TypeRespectingEmbedding A) :
    act A (SuccessorTree.SMTree.MMap.id (normalizedKptSMTree family)) f = f := by
  apply Subtype.ext
  rfl

theorem act_comp
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (f : TypeRespectingEmbedding A) :
    act A (SuccessorTree.SMTree.MMap.comp (normalizedKptSMTree family) F G) f =
      act A F (act A G f) := by
  apply Subtype.ext
  rfl

end TypeRespectingEmbedding

/-- Degree one for binary type-respecting full-profile approximations.

The source is any admissible finite partial structure, the continuation
condition is intrinsic, the auxiliary E relation is retained, and the colour
type is arbitrary finite. No extension or Ramsey hypothesis is assumed. -/
theorem normalizedKpt_typeRespectingRamsey
    {κ : Type*} [Fintype κ]
    (family : List (NormalizedForbidden db du dd))
    (A : FiniteTypeBase family)
    (colour : TypeRespectingEmbedding A → κ) :
    ∃ F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family),
      ∀ f g : TypeRespectingEmbedding A,
        colour (TypeRespectingEmbedding.act A F f) =
          colour (TypeRespectingEmbedding.act A F g) := by
  obtain ⟨F, hF⟩ := SuccessorTree.SMTree.boundedRestrictionRamsey
    (normalizedKptSMTree family) (fun u : TypeProfile A => u.1)
    (A.size + 1) (fun u => Nat.lt_succ_iff.mpr u.level_le_size)
    (fun f => colour (TypeRespectingEmbedding.ofRestriction A f))
  exact ⟨F, fun f g => hF (TypeRespectingEmbedding.toRestriction A f)
    (TypeRespectingEmbedding.toRestriction A g)⟩

end SuccessorTree.V10
