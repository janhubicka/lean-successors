import SuccessorTree.V10.FiniteTypeProfileContinuation
import SuccessorTree.V10.FiniteTypeProfileRecovery
import SuccessorTree.V10.PrescribedCompatibleCompletion

/-!
# Extending one finite compatible front through one target coordinate

The input is an intrinsic type-profile map. Its finite continuation condition
supplies precisely the age test required by the existing boring-extension
construction. A global map agreeing with the current front prefixes can
therefore extend those prefixes by one coordinate while preserving earlier
source levels. No global extendability of the intrinsic map is assumed.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {A B : FiniteTypeBase family}

namespace CoherentTypeProfileMap

/-- A target prefix of a member of one complete source front. -/
def frontPrefix (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (k : Nat) (hk : k ≤ (h.cutMap i).val)
    (T : TypeProfileFront A i) : PartialTypeWithE k db du dd :=
  (h T.toProfile).1.2.restrict (by
    rw [h.level_eq, TypeProfileFront.toProfile_cut]
    exact hk)

theorem frontPrefix_admissible (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (k : Nat) (hk : k ≤ (h.cutMap i).val)
    (T : TypeProfileFront A i) :
    IsAdmissibleRawType family
      (⟨k, h.frontPrefix i k hk T⟩ : RawPartialTypeNode db du dd) :=
  admissibleRawType_closed_under_prefix family (h T.toProfile).2 k _

theorem frontPrefix_restrict (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (k l : Nat)
    (hkl : k ≤ l) (hl : l ≤ (h.cutMap i).val)
    (T : TypeProfileFront A i) :
    (h.frontPrefix i l hl T).restrict hkl =
      h.frontPrefix i k (hkl.trans hl) T :=
  PartialTypeWithE.restrict_trans _ _ _

theorem frontPrefix_sameSocle (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (k : Nat) (hk : k ≤ (h.cutMap i).val)
    (T : TypeProfileFront A i) :
    SameOrdinaryAtCut (h.frontPrefix i k hk T) (B.str.partialTypeAt k 0) := by
  have hImage : k ≤ (h T.toProfile).1.1 := by
    rw [h.level_eq, TypeProfileFront.toProfile_cut]
    exact hk
  have hSame := h.maps_socle T.toProfile
  exact ⟨fun x y t => hSame.1
      ⟨x.val, lt_of_lt_of_le x.isLt hImage⟩
      ⟨y.val, lt_of_lt_of_le y.isLt hImage⟩ t,
    fun x t => hSame.2.1 ⟨x.val, lt_of_lt_of_le x.isLt hImage⟩ t,
    fun x t => hSame.2.2.1 ⟨x.val, lt_of_lt_of_le x.isLt hImage⟩ t,
    fun x y => hSame.2.2.2
      ⟨x.val, lt_of_lt_of_le x.isLt hImage⟩
      ⟨y.val, lt_of_lt_of_le y.isLt hImage⟩⟩

/-- Keeping the source cut coordinates in a target prefix recovers the
entire source record as soon as that prefix contains those coordinates. -/
theorem frontPrefix_recovers (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (k : Nat) (hk : k ≤ (h.cutMap i).val)
    (rho : Fin i.val → Fin k)
    (hRho : ∀ x : Fin i.val,
      (rho x).val = (h.cutMap ⟨x.val, by omega⟩).val)
    (T : TypeProfileFront A i) :
    (h.frontPrefix i k hk T).reindexOrdinary rho = T.val := by
  have hImage : k ≤ (h T.toProfile).1.1 := by
    rw [h.level_eq, TypeProfileFront.toProfile_cut]
    exact hk
  let rho' : Fin i.val → Fin (h T.toProfile).1.1 :=
    fun x => ⟨(rho x).val, lt_of_lt_of_le (rho x).isLt hImage⟩
  have hIndex : rho' = h.retainedIndex T.toProfile := by
    funext x
    apply Fin.ext
    exact hRho x
  have hRestrict : (h.frontPrefix i k hk T).reindexOrdinary rho =
      (h T.toProfile).1.2.reindexOrdinary rho' := by
    apply PartialTypeWithE.eq_of_atoms
    · apply RelationalPrefixType.eq_of_atoms
      · intro x y t
        cases x <;> cases y <;> rfl
      · intro x t
        cases x <;> rfl
      · intro x t
        cases x <;> rfl
    · intro x y
      cases x <;> cases y <;> rfl
  rw [hRestrict, hIndex]
  exact h.recovers_complete_record T.toProfile

/-- The one-coordinate prescription on the images of one complete front.
Its value is chosen from the finite front; injectivity of the current
prefixes will later identify it with the intended value for every member. -/
noncomputable def frontBoringData (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (m : Nat) (hm : m + 1 ≤ (h.cutMap i).val) :
    PrescribedBoringData m db du dd := by
  classical
  let sourceRecord := h.frontPrefix i m (by omega)
  let targetRecord := h.frontPrefix i (m + 1) hm
  let target : PartialTypeWithE m db du dd → PartialTypeWithE (m + 1) db du dd :=
    fun S => if hS : ∃ T : TypeProfileFront A i, sourceRecord T = S then
      targetRecord (Classical.choose hS)
    else
      { lReduct := { binary := fun _ _ _ => false
                     unary := fun _ _ => false
                     diagonal := fun _ _ => false }
        eRelation := fun _ _ => false }
  refine {
    source := Set.range sourceRecord
    target := target
    extendsSource := ?_
    preservesCompatibility := ?_ }
  · intro S hS
    change ∃ T : TypeProfileFront A i, sourceRecord T = S at hS
    simp only [target, dif_pos hS]
    exact (h.frontPrefix_restrict i m (m + 1) (Nat.le_succ m) hm _).trans
      (Classical.choose_spec hS)
  · intro S U hS hU _
    change ∃ T : TypeProfileFront A i, sourceRecord T = S at hS
    change ∃ T : TypeProfileFront A i, sourceRecord T = U at hU
    simp only [target, dif_pos hS, dif_pos hU]
    exact sameOrdinaryAtCut_trans
      (h.frontPrefix_sameSocle i (m + 1) hm (Classical.choose hS))
      (sameOrdinaryAtCut_symm
        (h.frontPrefix_sameSocle i (m + 1) hm (Classical.choose hU)))

theorem frontBoringData_target_exists (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (m : Nat) (hm : m + 1 ≤ (h.cutMap i).val)
    (S : PartialTypeWithE m db du dd) (hS : S ∈ (h.frontBoringData i m hm).source) :
    ∃ T : TypeProfileFront A i,
      (h.frontBoringData i m hm).target S = h.frontPrefix i (m + 1) hm T := by
  classical
  change ∃ T : TypeProfileFront A i,
    h.frontPrefix i m (by omega) T = S at hS
  refine ⟨Classical.choose hS, ?_⟩
  simp only [frontBoringData, dif_pos hS]

theorem frontBoringData_target_eq (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size + 1)) (m : Nat) (hm : m + 1 ≤ (h.cutMap i).val)
    (hInj : Function.Injective (h.frontPrefix i m (by omega)))
    (T : TypeProfileFront A i) :
    (h.frontBoringData i m hm).target (h.frontPrefix i m (by omega) T) =
      h.frontPrefix i (m + 1) hm T := by
  classical
  have hS : ∃ U : TypeProfileFront A i,
      h.frontPrefix i m (by omega) U = h.frontPrefix i m (by omega) T := ⟨T, rfl⟩
  have hChoose : Classical.choose hS = T := hInj (Classical.choose_spec hS)
  simp only [frontBoringData, dif_pos hS, hChoose]

end CoherentTypeProfileMap

namespace FiniteTypeProfileMap

/-- Every prescription drawn from prefixes of one transported complete
front satisfies the existing compatible boring-extension age test. The
source coordinates must all lie strictly before the inserted coordinate. -/
theorem compatibleB3_of_front_prefixes
    (h : FiniteTypeProfileMap A B) (i : Fin (A.size + 1))
    (m : Nat) (hm : m + 1 ≤ (h.cutMap i).val)
    (hRetained : ∀ x : Fin i.val,
      (h.cutMap ⟨x.val, by omega⟩).val < m)
    (D : PrescribedBoringData m db du dd)
    (hTargets : ∀ S, S ∈ D.source → ∃ T : TypeProfileFront A i,
      D.target S = h.toCoherentTypeProfileMap.frontPrefix i (m + 1) hm T) :
    D.CompatibleB3 family := by
  classical
  let f := h.toCoherentTypeProfileMap
  let q := m + 1
  let l := (h.cutMap i).val
  intro S0 hS0 W hFinite hSame hUpper hDelete
  obtain ⟨T0, hT0⟩ := hTargets S0 hS0
  have hSocle := f.frontPrefix_sameSocle i q hm T0
  have hOrdinaryB : ∀ x y : Fin q, ∀ t : Fin db,
      W.binary x.val y.val t = B.str.L.binary x.val y.val t := by
    intro x y t
    have hx : x.val ≤ m := by have hx := x.isLt; dsimp [q] at hx; omega
    have hy : y.val ≤ m := by have hy := y.isLt; dsimp [q] at hy; omega
    have hAtom := hSame.2.1 x.val y.val hx hy t
    have hAtom' : W.binary x.val y.val t =
        (D.target S0).lReduct.binary (some x) (some y) t := by
      simpa only [prescribedOrdinarySocle, dif_pos hx, dif_pos hy] using hAtom
    rw [hT0] at hAtom'
    exact hAtom'.trans (hSocle.1 x y t)
  have hOrdinaryU : ∀ x : Fin q, ∀ t : Fin du,
      W.unary x.val t = B.str.L.unary x.val t := by
    intro x t
    have hx : x.val ≤ m := by have hx := x.isLt; dsimp [q] at hx; omega
    have hAtom := hSame.2.2.1 x.val hx t
    have hAtom' : W.unary x.val t = (D.target S0).lReduct.unary (some x) t := by
      simpa only [prescribedOrdinarySocle, dif_pos hx] using hAtom
    rw [hT0] at hAtom'
    exact hAtom'.trans (hSocle.2.1 x t)
  have hOrdinaryD : ∀ x : Fin q, ∀ t : Fin dd,
      W.diagonal x.val t = B.str.L.diagonal x.val t := by
    intro x t
    have hx : x.val ≤ m := by have hx := x.isLt; dsimp [q] at hx; omega
    have hAtom := hSame.2.2.2 x.val hx t
    have hAtom' : W.diagonal x.val t = (D.target S0).lReduct.diagonal (some x) t := by
      simpa only [prescribedOrdinarySocle, dif_pos hx] using hAtom
    rw [hT0] at hAtom'
    exact hAtom'.trans (hSocle.2.2.1 x t)
  obtain ⟨N, hN⟩ := hFinite
  let P : Set (Fin N) := {a | q + a.val ∈ W.carrier}
  have hCarrier : ∀ x, x ∈ W.carrier ↔
      x < q ∨ ∃ a : Fin N, a ∈ P ∧ x = q + a.val := by
    intro x
    constructor
    · intro hx
      by_cases hLow : x < q
      · exact Or.inl hLow
      · have hxN := hN x hx
        let a : Fin N := ⟨x - q, by omega⟩
        have hAddress : x = q + a.val := by dsimp [a]; omega
        exact Or.inr ⟨a, by simpa only [P, Set.mem_setOf_eq, ← hAddress] using hx,
          hAddress⟩
    · rintro (hx | ⟨a, ha, rfl⟩)
      · have hxm : x ≤ m := by dsimp [q] at hx; omega
        exact (hSame.1 x hxm).2 (show x ≤ m from hxm)
      · exact ha
  by_cases hNonempty : P.Nonempty
  · have hLabelExists : ∀ a : Fin N, a ∈ P →
        ∃ T : TypeProfileFront A i,
          RelationalPrefixType.ofAgeModel W q (q + a.val) =
            (f.frontPrefix i q hm T).lReduct := by
      intro a ha
      obtain ⟨S, hS, _, hType⟩ := hUpper (q + a.val) ha (by dsimp [q]; omega)
      obtain ⟨T, hTarget⟩ := hTargets S hS
      refine ⟨T, ?_⟩
      change RelationalPrefixType.ofAgeModel W q (q + a.val) =
        (D.target S).lReduct at hType
      exact hType.trans (congrArg PartialTypeWithE.lReduct hTarget)
    let labels : Fin N → TypeProfileFront A i := fun a =>
      if ha : a ∈ P then Classical.choose (hLabelExists a ha) else T0
    have hLabel : ∀ a : Fin N, a ∈ P →
        RelationalPrefixType.ofAgeModel W q (q + a.val) =
          (f.frontPrefix i q hm (labels a)).lReduct := by
      intro a ha
      simpa only [labels, dif_pos ha] using Classical.choose_spec (hLabelExists a ha)
    let rho : Fin i.val → Fin q := fun x =>
      ⟨(h.cutMap ⟨x.val, by omega⟩).val, by
        have hBound := hRetained x
        dsimp [q]
        omega⟩
    have hRho : ∀ x : Fin i.val,
        (rho x).val = (h.cutMap ⟨x.val, by omega⟩).val := fun _ => rfl
    have hMono : StrictMono rho := by
      intro x y hxy
      exact h.cut_strictMono (show (⟨x.val, by omega⟩ : Fin (A.size + 1)) <
        ⟨y.val, by omega⟩ from hxy)
    let W0 := W.continuationPullback rho P
    have hW0Type : ∀ a : Fin N, a ∈ P →
        RelationalPrefixType.ofAgeModel W0 i.val (i.val + a.val) =
          (labels a).val.lReduct := by
      intro a ha
      rw [show RelationalPrefixType.ofAgeModel W0 i.val (i.val + a.val) =
          (RelationalPrefixType.ofAgeModel W q (q + a.val)).reindexOrdinary rho from
        W.continuationPullback_type rho P a, hLabel a ha]
      exact congrArg PartialTypeWithE.lReduct (f.frontPrefix_recovers i q hm rho hRho (labels a))
    obtain ⟨a0, ha0⟩ := hNonempty
    have hW0 : ProfileContinuation A i N P
        (fun a => (labels a).toProfile.1) W0 := by
      refine ⟨fun _ => Iff.rfl, ?_, ?_, ?_, ?_⟩
      · intro x y t
        have hAtom := congrArg (fun Q : RelationalPrefixType i.val db du dd =>
          Q.binary (some x) (some y) t) (hW0Type a0 ha0)
        exact hAtom.trans ((labels a0).property.2.1 x y t)
      · intro x t
        have hAtom := congrArg (fun Q : RelationalPrefixType i.val db du dd =>
          Q.unary (some x) t) (hW0Type a0 ha0)
        exact hAtom.trans ((labels a0).property.2.2.1 x t)
      · intro x t
        have hAtom := congrArg (fun Q : RelationalPrefixType i.val db du dd =>
          Q.diagonal (some x) t) (hW0Type a0 ha0)
        exact hAtom.trans ((labels a0).property.2.2.2.1 x t)
      · intro a ha
        exact congrArg (Sigma.mk i.val) (hW0Type a ha)
    have hLowIn : ∀ x : Fin i.val, (rho x).val ∈ (W.withoutVertex m).carrier := by
      intro x
      have hx : (rho x).val < m := hRetained x
      have hxW : (rho x).val ∈ W.carrier :=
        (hSame.1 _ (Nat.le_of_lt hx)).2 (show (rho x).val ≤ m from Nat.le_of_lt hx)
      exact ⟨hxW, Nat.ne_of_lt hx⟩
    have hUpperIn : ∀ a : Fin N, a ∈ P → q + a.val ∈ (W.withoutVertex m).carrier := by
      intro a ha
      exact ⟨ha, by dsimp [q]; omega⟩
    have hAvoid0 : ∀ bad, bad ∈ family → bad.Avoids W0 :=
      ((W.withoutVertex m).continuationPullback_induced rho P hMono hLowIn hUpperIn).preserves_avoidance family hDelete
    obtain ⟨V, hV, hSameUpper, hAvoidV⟩ :=
      h.age i N P (fun a => (labels a).toProfile) W0 hW0 hAvoid0
    let keep : Fin q → Fin l := fun x => ⟨x.val, lt_of_lt_of_le x.isLt hm⟩
    have hKeep : StrictMono keep := fun _ _ hxy => hxy
    have hWVType : ∀ a : Fin N, a ∈ P →
        RelationalPrefixType.ofAgeModel W q (q + a.val) =
          (RelationalPrefixType.ofAgeModel V l (l + a.val)).reindexOrdinary keep := by
      intro a ha
      have hPrefix := hV.upper_restrict a ha q hm
      change RelationalPrefixType.ofAgeModel V q (l + a.val) =
        (f.frontPrefix i q hm (labels a)).lReduct at hPrefix
      calc
        RelationalPrefixType.ofAgeModel W q (q + a.val) =
            (f.frontPrefix i q hm (labels a)).lReduct := hLabel a ha
        _ = RelationalPrefixType.ofAgeModel V q (l + a.val) := hPrefix.symm
        _ = (RelationalPrefixType.ofAgeModel V l (l + a.val)).reindexOrdinary keep := by
          rw [← RelationalPrefixType.ofAgeModel_restrict V q l (l + a.val) hm]
          apply RelationalPrefixType.eq_of_atoms
          · intro x y t
            cases x <;> cases y <;> rfl
          · intro x t
            cases x <;> rfl
          · intro x t
            cases x <;> rfl
    have hWV : SameUpperL W V q l N P :=
      (W.continuationPullback_sameUpper rho P).symm.trans hSameUpper
    obtain ⟨e⟩ := continuation_induced_of_types W V P keep hKeep ⟨a0, ha0⟩
      hCarrier hV.carrier hWVType hWV.binary
    exact e.preserves_avoidance family hAvoidV
  · have hLow : ∀ x, x ∈ W.carrier → x < q := by
      intro x hx
      rcases (hCarrier x).1 hx with hx | ⟨a, ha, _⟩
      · exact hx
      · exact (hNonempty ⟨a, ha⟩).elim
    let e : W.InducedEmbeddingOnCarrier B.str.L := {
      toFun := id
      order := fun _ _ _ _ hxy => hxy
      inside := by
        intro x hx
        have hxq := hLow x hx
        have hB := (h.cutMap i).isLt
        apply (B.str.carrier_iff x).2
        change x < B.size
        dsimp [q] at hxq
        omega
      binary := fun x y hx hy _ t =>
        (hOrdinaryB ⟨x, hLow x hx⟩ ⟨y, hLow y hy⟩ t).symm
      unary := fun x hx t => (hOrdinaryU ⟨x, hLow x hx⟩ t).symm
      diagonal := fun x hx t => (hOrdinaryD ⟨x, hLow x hx⟩ t).symm }
    exact e.preserves_avoidance family B.avoids

/-- Extend the current images of one complete source front by one target
coordinate. The existing global boring-extension theorem supplies the map;
the only age assumption is the intrinsic finite continuation condition. -/
theorem extend_front_once
    (h : FiniteTypeProfileMap A B) (n m : Nat) (hn : n ≤ A.size)
    (hnPos : 0 < n)
    (hLow : h.toCoherentTypeProfileMap.levelMap (n - 1) (by omega) < m)
    (hHigh : m < h.toCoherentTypeProfileMap.levelMap n hn)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (hAgree : ∀ u : TypeProfile A, u.level < n → F u.1 = h u)
    (hFront : ∀ u : TypeProfile A, u.level = n →
      (F u.1).1.1 = m ∧ F u.1 ≤ h u) :
    ∃ G : SuccessorTree.ShapeMap (admissibleKptSTree family),
      G ∈ KptM family ∧
      (∀ u : TypeProfile A, u.level < n → G u.1 = h u) ∧
      (∀ u : TypeProfile A, u.level = n →
        (G u.1).1.1 = m + 1 ∧ G u.1 ≤ h u) := by
  classical
  let f := h.toCoherentTypeProfileMap
  let i : Fin (A.size + 1) := ⟨n, Nat.lt_succ_iff.mpr hn⟩
  by_cases hNonempty : Nonempty (TypeProfileFront A i)
  · let T0 : TypeProfileFront A i := Classical.choice hNonempty
    have hm : m + 1 ≤ (h.cutMap i).val := Nat.succ_le_iff.mpr hHigh
    have hm0 : m ≤ (h.cutMap i).val := Nat.le_of_lt hHigh
    have hRetained : ∀ x : Fin i.val,
        (h.cutMap ⟨x.val, by omega⟩).val < m := by
      intro x
      have hx : x.val ≤ n - 1 := by have hx := x.isLt; change x.val < n at hx; omega
      exact lt_of_le_of_lt (f.levelMap_mono (by omega) (by omega) hx) hLow
    have hFraw : ∀ T : TypeProfileFront A i,
        (F T.toProfile.1).1 =
          (⟨m, f.frontPrefix i m hm0 T⟩ : RawPartialTypeNode db du dd) := by
      intro T
      obtain ⟨hLevel, hPrefix⟩ := hFront T.toProfile rfl
      have hImage : m ≤ (h T.toProfile).1.1 := by
        rw [h.level_eq, TypeProfileFront.toProfile_cut]
        exact hm0
      let v := admissibleKptAncestor (h T.toProfile) m hImage
      have hv : v ≤ h T.toProfile := admissibleKptAncestor_le _ _ _
      have hEq : F T.toProfile.1 = v := by
        rcases LevelTree.comparable_below hPrefix hv with hLe | hLe
        · exact LevelTree.same_level_of_le hLe hLevel
        · exact (LevelTree.same_level_of_le hLe hLevel.symm).symm
      exact congrArg Subtype.val hEq
    have hInj : Function.Injective (f.frontPrefix i m hm0) := by
      intro T U hTU
      apply TypeProfileFront.toProfile_injective
      apply Subtype.ext
      apply F.injective
      apply Subtype.ext
      rw [hFraw T, hFraw U]
      exact congrArg (Sigma.mk m) hTU
    let D := f.frontBoringData i m hm
    have hB3 : D.CompatibleB3 family :=
      h.compatibleB3_of_front_prefixes i m hm hRetained D
        (fun S hS => f.frontBoringData_target_exists i m hm S hS)
    have hTargets : ∀ S, S ∈ D.source → IsAdmissibleRawType family
        (⟨m + 1, D.target S⟩ : RawPartialTypeNode db du dd) := by
      intro S hS
      obtain ⟨T, hT⟩ := f.frontBoringData_target_exists i m hm S hS
      rw [hT]
      exact f.frontPrefix_admissible i (m + 1) hm T
    have hmPos : 0 < m := by omega
    obtain ⟨J, hJM, hSkip, hJ⟩ :=
      D.compatible_boring_extension_exists family hB3 hTargets hmPos
    let G := J.comp F
    have hGraw : ∀ T : TypeProfileFront A i,
        (G T.toProfile.1).1 =
          (⟨m + 1, f.frontPrefix i (m + 1) hm T⟩ : RawPartialTypeNode db du dd) := by
      intro T
      let S := f.frontPrefix i m hm0 T
      have hS : S ∈ D.source := ⟨T, rfl⟩
      have hAd : IsAdmissibleRawType family
          (⟨m, S⟩ : RawPartialTypeNode db du dd) :=
        f.frontPrefix_admissible i m hm0 T
      have hFS : F T.toProfile.1 =
          (⟨⟨m, S⟩, hAd⟩ : AdmissibleKptNode family) := Subtype.ext (hFraw T)
      change (J (F T.toProfile.1)).1 = _
      rw [hFS, hJ S hS hAd]
      exact congrArg (Sigma.mk (m + 1))
        (f.frontBoringData_target_eq i m hm hInj T)
    refine ⟨G, kptM_comp_mem family hJM hFM, ?_, ?_⟩
    · intro u hu
      have hSmall : (F u.1).1.1 < m := by
        have hStrict := F.level_lt_of_level_lt
          (show LevelTree.lev u.1 < LevelTree.lev T0.toProfile.1 from hu)
        have hTop := (hFront T0.toProfile rfl).1
        exact hTop ▸ hStrict
      change J (F u.1) = h u
      rw [kptShapeMap_fixed_below_skip family J m hSkip (F u.1) hSmall]
      exact hAgree u hu
    · intro u hu
      obtain ⟨T, hT⟩ := u.exists_front i hu
      subst u
      have hRaw := hGraw T
      refine ⟨congrArg Sigma.fst hRaw, ?_⟩
      change (G T.toProfile.1).1 ≤ (h T.toProfile).1
      rw [hRaw]
      refine ⟨?_, rfl⟩
      rw [h.level_eq, TypeProfileFront.toProfile_cut]
      exact hm
  · refine ⟨F, hFM, hAgree, ?_⟩
    intro u hu
    obtain ⟨T, _⟩ := u.exists_front i hu
    exact (hNonempty ⟨T⟩).elim

end FiniteTypeProfileMap

end SuccessorTree.V10
