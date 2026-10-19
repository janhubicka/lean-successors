import SuccessorTree.V10.FiniteTypeProfileCap
import SuccessorTree.V10.GPlusShapeActionFoundation

/-!
# The intrinsic finite restriction of a global Kpt map

The target base is the entire ordinary socle of the image of a neutral cap.
In particular its size is the image of the terminal source cut. This differs
from the shorter cut used by the induced action on G+ vertices.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace AdmissibleKptNode

/-- The full ordinary finite base of an admissible node, also at level zero. -/
noncomputable def finiteTypeBase (N : AdmissibleKptNode family) :
    FiniteTypeBase family where
  str := N.witnessStructure.initialSegment N.1.1 N.level_le_witness_size
  avoids := N.witnessStructure.initialSegment_avoids family
    N.witness_spec.2.1 N.1.1 N.level_le_witness_size

@[simp] theorem finiteTypeBase_size (N : AdmissibleKptNode family) :
    N.finiteTypeBase.size = N.1.1 := rfl

/-- Every prefix has precisely the corresponding initial ordinary socle. -/
theorem prefix_finiteTypeBase_socle {u N : AdmissibleKptNode family}
    (hu : u ≤ N) :
    SameOrdinaryAtCut u.1.2
      (N.finiteTypeBase.str.partialTypeAt u.1.1 0) := by
  let D := N.witnessStructure
  let v := N.witnessVertex
  have hRaw : N.1 = D.rawTypeAtFree v := N.witness_spec.2.2
  have hCut : N.1.1 = D.freeLevel v := congrArg Sigma.fst hRaw
  have hTyped : N.1 = (⟨N.1.1, D.partialTypeAt N.1.1 v⟩ :
      RawPartialTypeNode db du dd) := by
    calc
      N.1 = D.rawTypeAtFree v := hRaw
      _ = (⟨N.1.1, D.partialTypeAt N.1.1 v⟩ :
          RawPartialTypeNode db du dd) := by
        change (⟨D.freeLevel v, D.partialTypeAt (D.freeLevel v) v⟩ :
          RawPartialTypeNode db du dd) = _
        rw [← hCut]
  have hRecord : N.1.2 = D.partialTypeAt N.1.1 v :=
    eq_of_heq (Sigma.mk.inj_iff.mp hTyped).2
  rw [hu.2, hRecord]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro i j
    change D.E i.val j.val =
      if j.val < N.1.1 then D.E i.val j.val else false
    rw [if_pos (lt_of_lt_of_le j.isLt hu.1)]

end AdmissibleKptNode

namespace FiniteTypeBase

/-- The entire finite target ordinary socle of a global profile restriction. -/
noncomputable def shapeImage (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    FiniteTypeBase family :=
  (F (TypeProfile.cap A).1).finiteTypeBase

@[simp] theorem shapeImage_size (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family)) :
    (A.shapeImage F).size = kptShapeLevelMap family F A.size :=
  (kptShapeLevelMap_eq family F (TypeProfile.cap A).1).symm

end FiniteTypeBase

private theorem sameOrdinary_cast_initial {n m : Nat} (e : n = m)
    (T : PartialTypeWithE m db du dd)
    (D : EnumeratedPartialStructure db du dd)
    (h : SameOrdinaryAtCut T (D.partialTypeAt m 0)) :
    SameOrdinaryAtCut
      (cast (congrArg (fun k => PartialTypeWithE k db du dd) e.symm) T)
      (D.partialTypeAt n 0) := by
  cases e
  exact h

namespace CoherentTypeProfileMap

/-- A global root-normalized shape map sends a full source profile to one
full target profile, including all unrealized source types. -/
theorem shapeMap_maps_socle (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family) (u : TypeProfile A) :
    SameOrdinaryAtCut (F u.1).1.2
      ((A.shapeImage F).str.partialTypeAt (F u.1).1.1 0) := by
  by_cases hZero : u.level = 0
  · have hImage : (F u.1).1.1 = 0 := hF u.1 hZero
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i
    all_goals have hi := i.isLt; omega
  · let c : TypeProfile A := TypeProfile.atCut A u.level u.level_le_size
    have hComp : SameOrdinaryAtCut u.1.1.2 c.1.1.2 :=
      sameOrdinaryAtCut_trans u.same_socle (sameOrdinaryAtCut_symm c.same_socle)
    obtain ⟨heq, hc⟩ := shapeMap_preserves_source_compatibility family F
      u.1.1.2 c.1.1.2 (Nat.pos_of_ne_zero hZero) u.1.2 c.1.2 hComp
    have hCap : c.1 ≤ (TypeProfile.cap A).1 :=
      admissibleKptAncestor_le _ _ _
    have hSocle := AdmissibleKptNode.prefix_finiteTypeBase_socle
      (F.map_le_of_le hCap)
    exact sameOrdinaryAtCut_trans hc
      (sameOrdinary_cast_initial heq (F c.1).1.2
        (A.shapeImage F).str hSocle)

/-- Literal restriction of a global monoid map, with its finite coherent
certificate. The age clause is established separately by finite transport. -/
noncomputable def ofShapeMap (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family) : CoherentTypeProfileMap A (A.shapeImage F) where
  toFun := fun u => F u.1
  injective' := by
    intro u v huv
    exact Subtype.ext (F.injective huv)
  cutMap := fun i => ⟨kptShapeLevelMap family F i.val, by
    rw [A.shapeImage_size]
    exact Nat.lt_succ_iff.mpr
      ((kptShapeLevelMap_strictMono family F).monotone
        (Nat.le_of_lt_succ i.isLt))⟩
  cut_strictMono := by
    intro i j hij
    exact kptShapeLevelMap_strictMono family F hij
  cut_zero := by
    apply Fin.ext
    let r := TypeProfile.atCut A 0 (Nat.zero_le _)
    exact (kptShapeLevelMap_eq family F r.1).trans (hF r.1 rfl)
  cut_top := by
    apply Fin.ext
    exact (A.shapeImage_size F).symm
  level_eq := fun u => (kptShapeLevelMap_eq family F u.1).symm
  maps_socle := shapeMap_maps_socle A F hF
  root_fixed := fun u hu => kptM_fixes_roots family hF u.1 hu
  «prefix» := fun _ _ huv => F.map_le_of_le huv
  weak_succ := by
    intro u v p c hStep
    obtain ⟨d, hd, hdv⟩ := F.weak_succ' hStep
    refine ⟨d, ?_, hdv⟩
    simpa only [List.map_map, Function.comp_def] using hd

@[simp] theorem ofShapeMap_apply (A : FiniteTypeBase family)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family) (u : TypeProfile A) :
    ofShapeMap A F hF u = F u.1 := rfl

end CoherentTypeProfileMap
end SuccessorTree.V10
