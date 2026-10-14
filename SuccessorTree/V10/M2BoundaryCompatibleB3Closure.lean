import SuccessorTree.V10.M2BoundaryOriginalCompatibility
import SuccessorTree.V10.M2BoundaryFinalCriterion
import Mathlib.Tactic

/-!
# The finite compatible B3 test for the actual M2 boundary prescription

Let F be a genuine admissible Kpt ShapeMap with a skipped target
level m immediately before the first affected source level n.
The canonical prescribed boundary map has source all actual D(x)
records at source level n and target the actual F(x) records.

Suppose an arbitrary FINITE ORDERED L-age witness W meets the
corrected compatible B3 test but has an induced forbidden copy.
A copy entirely in the prescribed lower socle contradicts
admissibility of its target type. Otherwise pick its actual upper
vertices. Every allowed upper L type is an F-image of a genuine
source node. D-compatibility reflects to the original source L+
socle; complete retained records recover the lower--lower atoms.
The previously proved simultaneous nonedge padding and induced
copy theorem now puts the whole forbidden pattern in one admissible
F-image cap, a contradiction.

No E expansion of W, no M2 axiom, and no assumed B3/age-preservation
condition on an arbitrary map are used.
-/

namespace SuccessorTree.V10

/-- The ACTUAL boundary B1/B2 prescription of ANY genuine Kpt ShapeMap
satisfies the corrected finite L-only CompatibleB3 age condition. -/
theorem m2Boundary_actual_compatibleB3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    (m2Boundary_prescribedData family F q₀ a₀ hprev hgap).CompatibleB3 family := by
  classical
  let n := LevelTree.lev a₀
  let m := LevelTree.lev (F a₀)-1
  let lambda := kptShapeLevelMap family F
  let Pdata := m2Boundary_prescribedData family F q₀ a₀ hprev hgap
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  have hCut : lambda n = m+1 := by
    dsimp [lambda,n,m]
    rw [kptShapeLevelMap_eq family F a₀]
    omega
  have hBelow : ∀ i, i < n → lambda i < m := by
    intro i hi
    have hIQ : i ≤ LevelTree.lev q₀ := by
      dsimp [n] at hi
      omega
    have hLe := (kptShapeLevelMap_strictMono family F).monotone hIQ
    have hQ := kptShapeLevelMap_eq family F q₀
    dsimp [lambda,m]
    omega
  intro S0 hS0 W _hFinite hSame hUpper hDelete bad hBad
  have hTargetAd : IsAdmissibleRawType family
      (⟨m+1,Pdata.target S0⟩ :
        RawPartialTypeNode db du dd) :=
    m2Boundary_prescribed_targets_admissible
      family F q₀ a₀ hprev hgap S0 hS0
  have hAvoidSocle :=
    prescribedOrdinarySocle_avoids_of_admissible family
      (Pdata.target S0) hTargetAd
  cases bad with
  | singleton Q hNeutral =>
      rintro ⟨e,hCopy⟩
      have hAbove : ∃ a : Fin 1, m < e a :=
        forbiddenCopy_has_upper_of_sameInitialL
          W (prescribedOrdinarySocle (Pdata.target S0))
          m Q e hSame
          (hAvoidSocle (.singleton Q hNeutral) hBad) hCopy
      have hAway : ∀ a : Fin 1, e a ≠ m := by
        intro a
        obtain ⟨b,hb⟩ := hAbove
        have hab : a = b := Subsingleton.elim _ _
        rw [hab]
        omega
      have hCopyWithout : (W.withoutVertex m).Realizes Q e := by
        rcases hCopy with ⟨hMono,hIn,hBin,hUn,hDiag⟩
        exact ⟨hMono,fun a => ⟨hIn a,hAway a⟩,hBin,hUn,hDiag⟩
      exact (hDelete (.singleton Q hNeutral) hBad) ⟨e,hCopyWithout⟩
  | nontrivial r Q hr hIrred =>
      rintro ⟨e,hCopy⟩
      have hAbove : ∃ a : Fin r, m < e a :=
        m2B3_nontrivial_copy_has_upper
          family (Pdata.target S0) hTargetAd W
          Q hr hIrred hBad e hSame hCopy
      obtain ⟨i0,hi0,hTarget0⟩ :=
        m2Boundary_base_has_source_index
          family F q₀ a₀ hprev hgap S0 hS0
      let anchor := m2Boundary_originalType family a₀ i0
      have hAnchor : IsAdmissibleRawType family
          (⟨n,anchor⟩ : RawPartialTypeNode db du dd) :=
        m2Boundary_original_admissible family a₀ i0
      have hSameBase :
          SameInitialL W
            (prescribedOrdinarySocle
              (m2Boundary_targetType family F q₀ a₀ hprev hgap i0)) m := by
        simpa only [hTarget0] using hSame
      have hCarrier : ∀ k, k ≤ m → k ∈ W.carrier := by
        intro k hk
        apply (hSame.1 k hk).2
        change k ≤ m
        exact hk
      have hEach :
          ∀ (a : Fin r) (ha : m < e a),
            ∃ i : M2BoundaryIndex family a₀,
              SameOrdinaryAtCut
                (m2Boundary_sourceType family F q₀ a₀ hprev hgap i) S0 ∧
              RelationalPrefixType.ofAgeModel W (m+1) (e a) =
                (m2Boundary_targetType family F q₀ a₀ hprev hgap i).lReduct := by
        intro a ha
        exact m2Boundary_upper_vertex_has_source_index
          family F q₀ a₀ hprev hgap S0 W hUpper (e a)
            (hCopy.2.1 a) ha
      let ix (a : Fin r) (ha : m < e a) : M2BoundaryIndex family a₀ :=
        Classical.choose (hEach a ha)
      have hChosen (a : Fin r) (ha : m < e a) :
          SameOrdinaryAtCut
            (m2Boundary_sourceType family F q₀ a₀ hprev hgap (ix a ha)) S0 ∧
          RelationalPrefixType.ofAgeModel W (m+1) (e a) =
            (m2Boundary_targetType family F q₀ a₀ hprev hgap (ix a ha)).lReduct :=
        Classical.choose_spec (hEach a ha)
      let T : Fin r → PartialTypeWithE n db du dd := fun a =>
        if ha : m < e a then
          m2Boundary_originalType family a₀ (ix a ha)
        else anchor
      have hT (a : Fin r) (ha : m < e a) :
          T a = m2Boundary_originalType family a₀ (ix a ha) := by
        simp only [T, dite_eq_left ha]
      have hAd : ∀ (a : Fin r), m < e a →
          IsAdmissibleRawType family
            (⟨n,T a⟩ : RawPartialTypeNode db du dd) := by
        intro a ha
        rw [hT a ha]
        exact m2Boundary_original_admissible family a₀ (ix a ha)
      have hComp : ∀ (a : Fin r), m < e a →
          SameOrdinaryAtCut anchor (T a) := by
        intro a ha
        have hDeleted : SameOrdinaryAtCut
            (m2Boundary_sourceType family F q₀ a₀ hprev hgap i0)
            (m2Boundary_sourceType family F q₀ a₀ hprev hgap (ix a ha)) := by
          rw [hi0]
          exact sameOrdinaryAtCut_symm (hChosen a ha).1
        have hOriginal :=
          m2Boundary_original_compatible_of_deleted
            family F q₀ a₀ hprev hgap i0 (ix a ha) hDeleted
        rw [hT a ha]
        exact hOriginal
      have hInitial :
          ∀ (x y : Nat) (hx : x < n) (hy : y < n)
            (t : Fin db),
            W.binary (lambda x) (lambda y) t =
              anchor.lReduct.binary
                (some ⟨x,hx⟩) (some ⟨y,hy⟩) t := by
        intro x y hx hy t
        let i : Fin n := ⟨x,hx⟩
        let j : Fin n := ⟨y,hy⟩
        exact m2Boundary_initial_binary_of_sameSocle
          family F q₀ a₀ hprev hgap i0 W hSameBase
            i j t (hBelow x hx) (hBelow y hy)
      have hImage : ∀ (a : Fin r) (ha : m < e a),
          let u : AdmissibleKptNode family :=
            ⟨⟨n,T a⟩,hAd a ha⟩
          RelationalPrefixType.ofAgeModel W (LevelTree.lev (F u)) (e a) =
            (F u).1.2.lReduct := by
        intro a ha
        let u : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
        have hu : u = (ix a ha).1 := by
          apply Subtype.ext
          change (⟨n,T a⟩ : RawPartialTypeNode db du dd) =
            (ix a ha).1.1
          rw [hT a ha]
          exact (m2Boundary_original_raw family a₀ (ix a ha)).symm
        have hSelected :=
          m2Boundary_upper_L_type_of_source_index
            family F q₀ a₀ hprev hgap (ix a ha)
            W (e a) (hChosen a ha).2
        change RelationalPrefixType.ofAgeModel W
          (LevelTree.lev (F u)) (e a) = (F u).1.2.lReduct
        rw [hu]
        exact hSelected
      exact m2B3_selected_upper_forbidden_contradiction
        family F W e anchor hAnchor T hnPos hCut hBelow hCarrier hDelete
        hAd hComp hInitial hImage Q hr hIrred hBad hCopy hAbove

/-- The genuine two-map first-gap factorization in normalized Kpt:
its former sole finite-age CompatibleB3 premise is now derived from
the actual F-boundary prescription. No M2 field is imported. -/
theorem m2_actual_first_gap_factorization
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (q₀ a₀ : AdmissibleKptNode family)
    (hprev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hgap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀)) :
    ∃ F1 F2 : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F1 ∈ KptM family ∧
      F2 ∈ KptM family ∧
      F2.SkipsOnly (LevelTree.lev (F a₀)-1) ∧
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ LevelTree.lev a₀ →
        F2 (F1 x) = F x := by
  exact m2_factorization_of_actual_boundary_compatibleB3
    family F hFM q₀ a₀ hprev hgap
    (m2Boundary_actual_compatibleB3 family F q₀ a₀ hprev hgap)

end SuccessorTree.V10
