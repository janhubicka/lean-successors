import SuccessorTree.V10.M2JointImageCompatibility
import SuccessorTree.V10.M2TwoTypePaddedWitness
import Mathlib.Tactic

/-!
# Source nonedge amalgamation implies full image ordinary-socle compatibility

Two source types compatible in the full ordinary L+ record are first
jointly realized by one actual forbidden-free padded partial structure.
The checked cap provides one admissible type containing both ordinary
vertices. Applying the true canonical-parameter image lemma in that
single containing node shows equality of their complete target
ordinary L+ socles. No B3 or M2 axiom enters this proof.
-/
namespace SuccessorTree.V10

/-- A source partial type that is admissible at level n can occur in
an ambient partial structure only if the ambient E free cut is at
least n. This proof uses the full E record, not merely the L-reduct. -/
theorem partialTypeAt_freeLevel_ge_of_admissible
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (B : EnumeratedPartialStructure db du dd)
    (j : Nat) (T : PartialTypeWithE n db du dd)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hEq : B.partialTypeAt n j = T) :
    n ≤ B.freeLevel j := by
  by_contra hNot
  have hk : B.freeLevel j < n := by omega
  let k : Fin n := ⟨B.freeLevel j, hk⟩
  have hAd : T.eRelation (some k) none = true :=
    (NonedgePadding.admissible_type_E family T hT).1 k
  have hEqBit := congrArg
    (fun Q : PartialTypeWithE n db du dd =>
       Q.eRelation (some k) none) hEq
  have hBad : B.E (B.freeLevel j) j = true := by
    change B.E k.val j = T.eRelation (some k) none at hEqBit
    exact hEqBit.trans hAd
  have hMiss : B.E (B.freeLevel j) j = false :=
    B.freeLevel_firstMissing j
  rw [hMiss] at hBad
  cases hBad

/-- A pair of compatible admissible source types has compatible
image ordinary L+ socles under any genuine Kpt ShapeMap. The equality
proof is explicit because image records have dependent lengths. -/
theorem shapeMap_preserves_source_compatibility
    {n db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (T U : PartialTypeWithE n db du dd)
    (hn : 0 < n)
    (hT : IsAdmissibleRawType family
      (⟨n,T⟩ : RawPartialTypeNode db du dd))
    (hU : IsAdmissibleRawType family
      (⟨n,U⟩ : RawPartialTypeNode db du dd))
    (hComp : SameOrdinaryAtCut T U) :
    let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
    let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
    ∃ h : LevelTree.lev (F ti) = LevelTree.lev (F tj),
      SameOrdinaryAtCut (F ti).1.2
        (cast (congrArg (fun k => PartialTypeWithE k db du dd)
          h.symm) (F tj).1.2) := by
  let ti : AdmissibleKptNode family := ⟨⟨n,T⟩,hT⟩
  let tj : AdmissibleKptNode family := ⟨⟨n,U⟩,hU⟩
  obtain ⟨B,hAvoidB,hSize,hTypeI,hTypeJ⟩ :=
    twoCompatibleTypes_joint_padded family T U hT hU hComp
  let i := NonedgePadding.address n n
  let j := NonedgePadding.address n (n+1)
  have hi : i < B.size := by
    rw [hSize]
    exact NonedgePadding.address_lt_size n (n+2) n (by omega)
  have hj : j < B.size := by
    rw [hSize]
    exact NonedgePadding.address_lt_size n (n+2) (n+1) (by omega)
  have hni : n ≤ i := by
    simp only [i, NonedgePadding.address]
    split_ifs <;> omega
  have hnj : n ≤ j := by
    simp only [j, NonedgePadding.address]
    split_ifs <;> omega
  have hFreeI : n ≤ B.freeLevel i :=
    partialTypeAt_freeLevel_ge_of_admissible family B i T hT hTypeI
  have hFreeJ : n ≤ B.freeLevel j :=
    partialTypeAt_freeLevel_ge_of_admissible family B j U hU hTypeJ
  let A := NonedgePadding.socleCap B
  let v := B.size+1
  let u := NonedgePadding.socleCapNode family B hAvoidB
  have hv : v < A.size := by change B.size+1 < B.size+2; omega
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    NonedgePadding.socleCap_avoids family B hAvoidB
  have hCut : A.freeLevel v = B.size :=
    NonedgePadding.socleCap_freeLevel B
  have hiCut : i+1 ≤ A.freeLevel v := by rw [hCut]; omega
  have hjCut : j+1 ≤ A.freeLevel v := by rw [hCut]; omega
  have hiFree : A.freeLevel i = B.freeLevel i :=
    NonedgePadding.socleCap_old_freeLevel B i hi
  have hjFree : A.freeLevel j = B.freeLevel j :=
    NonedgePadding.socleCap_old_freeLevel B j hj
  have hiN : n ≤ A.freeLevel i := by rw [hiFree]; exact hFreeI
  have hjN : n ≤ A.freeLevel j := by rw [hjFree]; exact hFreeJ
  have hiPos : 0 < A.freeLevel i := by omega
  have hjPos : 0 < A.freeLevel j := by omega
  have hu : u.1 = A.rawTypeAtFree v := by
    change (⟨B.size, A.partialTypeAt B.size v⟩ : RawPartialTypeNode db du dd) =
      (⟨A.freeLevel v, A.partialTypeAt (A.freeLevel v) v⟩ : RawPartialTypeNode db du dd)
    rw [hCut]
  have hti : ti.1 =
      (⟨n, A.partialTypeAt n i⟩ : RawPartialTypeNode db du dd) := by
    apply congrArg (Sigma.mk n)
    calc
      T = B.partialTypeAt n i := hTypeI.symm
      _ = A.partialTypeAt n i :=
        (NonedgePadding.socleCap_partialTypeAt B n i hni hi).symm
  have htj : tj.1 =
      (⟨n, A.partialTypeAt n j⟩ : RawPartialTypeNode db du dd) := by
    apply congrArg (Sigma.mk n)
    calc
      U = B.partialTypeAt n j := hTypeJ.symm
      _ = A.partialTypeAt n j :=
        (NonedgePadding.socleCap_partialTypeAt B n j hnj hj).symm
  exact shapeMap_compatible_of_joint_ambient family F A v i j n
    hv hAvoidA hiCut hjCut hiPos hjPos hiN hjN
    u ti tj hu hti htj

end SuccessorTree.V10
