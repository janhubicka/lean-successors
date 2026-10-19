import SuccessorTree.V10.FiniteTypeProfile
import SuccessorTree.V10.M2SelectedCapTransport
import SuccessorTree.V10.M2CapPaddedRecords
import SuccessorTree.V10.M2ImageLowerSocle
import Mathlib.Tactic

/-!
# Global shape maps preserve finite labelled continuation ages

The forward implication uses the existing nonedge padding construction:
realize the finitely many prescribed full types simultaneously, place the
result in one capped admissible node, and apply the actual shape map.
Canonical parameter transport identifies complete image types, including
all coordinates skipped by the level map. No age-preservation assumption
on the global map is used.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

private theorem fillNeutralCarrier_type
    (W : AgeTestModel db du dd) (N n w : Nat)
    (hLow : ∀ x, x < n → x ∈ W.carrier)
    (hw : w ∈ W.carrier) :
    RelationalPrefixType.ofAgeModel (W.fillNeutralCarrier N) n w =
      RelationalPrefixType.ofAgeModel W n w := by
  have hIn (x : Option (Fin n)) : prefixVertexIndex w x ∈ W.carrier := by
    cases x with
    | none => exact hw
    | some x => exact hLow x.val x.isLt
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    exact W.fillNeutralCarrier_old_binary N _ _ (hIn x) (hIn y) t
  · intro x t
    exact W.fillNeutralCarrier_old_unary N _ (hIn x) t
  · intro x t
    exact W.fillNeutralCarrier_old_diagonal N _ (hIn x) t

/-- A selected image type gives every atom involving the lower socle;
the only remaining data are the binary atoms between two upper vertices. -/
private theorem continuation_embeds_in_image_type
    {N n q r : Nat} (Q : PartialTypeWithE N db du dd)
    (V : AgeTestModel db du dd) (P : Set (Fin r))
    (lambda : Nat → Nat) (hLambda : StrictMono lambda)
    (hCut : lambda n = q)
    (hCarrier : ∀ x, x ∈ V.carrier ↔
      x < q ∨ ∃ a : Fin r, a ∈ P ∧ x = q + a.val)
    (hNonempty : P.Nonempty)
    (hUpper : ∀ a : Fin r, a ∈ P →
      ∃ (hj : lambda (NonedgePadding.address n (n+a.val)) < N)
        (hq : q ≤ N),
        (Q.ordinaryType (lambda (NonedgePadding.address n (n+a.val)))
          hj q hq).lReduct =
            RelationalPrefixType.ofAgeModel V q (q+a.val))
    (hBinary : ∀ a b : Fin r, a ∈ P → b ∈ P → ∀ t : Fin db,
      Q.ageModel.binary
        (lambda (NonedgePadding.address n (n+a.val)))
        (lambda (NonedgePadding.address n (n+b.val))) t =
          V.binary (q+a.val) (q+b.val) t) :
    Nonempty (V.InducedEmbeddingOnCarrier Q.ageModel) := by
  classical
  obtain ⟨a0,ha0⟩ := hNonempty
  obtain ⟨hj0,hq0,hType0⟩ := hUpper a0 ha0
  obtain ⟨hLowB,hLowU,hLowD⟩ :=
    image_ordinary_type_all_lower_atoms Q _ hj0 hq0 V _ hType0
  let phi : Nat → Nat := fun x =>
    if x < q then x else lambda (NonedgePadding.address n (n+(x-q)))
  have hPhiLow (x : Nat) (hx : x < q) : phi x = x := by
    simp [phi,hx]
  have hPhiUpper (a : Fin r) :
      phi (q+a.val) = lambda (NonedgePadding.address n (n+a.val)) := by
    simp [phi]
  have hUpperGe (a : Fin r) :
      q ≤ lambda (NonedgePadding.address n (n+a.val)) := by
    rw [←hCut]
    apply hLambda.monotone
    simp only [NonedgePadding.address]
    split_ifs <;> omega
  have hUpperMono (a b : Fin r) (hab : a.val < b.val) :
      lambda (NonedgePadding.address n (n+a.val)) <
        lambda (NonedgePadding.address n (n+b.val)) := by
    apply hLambda
    simp only [NonedgePadding.address]
    split_ifs <;> omega
  refine ⟨{
    toFun := phi
    order := ?_
    inside := ?_
    binary := ?_
    unary := ?_
    diagonal := ?_ }⟩
  · intro x y hx hy hxy
    rcases (hCarrier x).1 hx with hx | ⟨a,ha,rfl⟩
    · rcases (hCarrier y).1 hy with hy | ⟨b,hb,rfl⟩
      · rw [hPhiLow x hx,hPhiLow y hy]
        exact hxy
      · rw [hPhiLow x hx,hPhiUpper]
        exact lt_of_lt_of_le hx (hUpperGe b)
    · rcases (hCarrier y).1 hy with hy | ⟨b,hb,rfl⟩
      · omega
      · rw [hPhiUpper,hPhiUpper]
        exact hUpperMono a b (by omega)
  · intro x hx
    rcases (hCarrier x).1 hx with hx | ⟨a,ha,rfl⟩
    · rw [hPhiLow x hx]
      change x ≤ N
      omega
    · rw [hPhiUpper]
      change lambda (NonedgePadding.address n (n+a.val)) ≤ N
      obtain ⟨hj,_,_⟩ := hUpper a ha
      exact Nat.le_of_lt hj
  · intro x y hx hy hne t
    rcases (hCarrier x).1 hx with hx | ⟨a,ha,rfl⟩
    · rcases (hCarrier y).1 hy with hy | ⟨b,hb,rfl⟩
      · rw [hPhiLow x hx,hPhiLow y hy]
        exact hLowB x y hx hy t
      · rw [hPhiLow x hx,hPhiUpper]
        obtain ⟨hj,hq,hType⟩ := hUpper b hb
        exact ((image_ordinary_type_all_low_upper_atoms Q _ hj hq V _ hType).1
          x hx t).1
    · rcases (hCarrier y).1 hy with hy | ⟨b,hb,rfl⟩
      · rw [hPhiUpper,hPhiLow y hy]
        obtain ⟨hj,hq,hType⟩ := hUpper a ha
        exact ((image_ordinary_type_all_low_upper_atoms Q _ hj hq V _ hType).1
          y hy t).2
      · rw [hPhiUpper,hPhiUpper]
        exact hBinary a b ha hb t
  · intro x hx t
    rcases (hCarrier x).1 hx with hx | ⟨a,ha,rfl⟩
    · rw [hPhiLow x hx]
      exact hLowU x hx t
    · rw [hPhiUpper]
      obtain ⟨hj,hq,hType⟩ := hUpper a ha
      exact (image_ordinary_type_all_low_upper_atoms Q _ hj hq V _ hType).2.2.1 t
  · intro x hx t
    rcases (hCarrier x).1 hx with hx | ⟨a,ha,rfl⟩
    · rw [hPhiLow x hx]
      exact hLowD x hx t
    · rw [hPhiUpper]
      obtain ⟨hj,hq,hType⟩ := hUpper a ha
      exact (image_ordinary_type_all_low_upper_atoms Q _ hj hq V _ hType).2.2.2 t

private theorem ordinary_type_relational_sigma
    {N q : Nat} (Q : PartialTypeWithE N db du dd)
    (j : Nat) (hj : j < N) (u : AdmissibleKptNode family)
    (hu : u.1.1 ≤ N)
    (hType : Q.ordinaryType j hj u.1.1 hu = u.1.2)
    (hLevel : q = u.1.1) :
    ∃ hq : q ≤ N,
      (⟨q,(Q.ordinaryType j hj q hq).lReduct⟩ :
        RawRelationalTypeNode db du dd) = u.relationalNode := by
  subst q
  exact ⟨hu,by rw [hType]; rfl⟩

private def continuationPullback
    (Q : AgeTestModel db du dd) (q r : Nat) (P : Set (Fin r))
    (phi : Nat → Nat) : AgeTestModel db du dd where
  carrier := {x | x < q ∨ ∃ a : Fin r, a ∈ P ∧ x = q+a.val}
  binary := fun x y t => Q.binary (phi x) (phi y) t
  unary := fun x t => Q.unary (phi x) t
  diagonal := fun x t => Q.diagonal (phi x) t

private theorem continuationPullback_type
    {N q r : Nat} (Q : PartialTypeWithE N db du dd)
    (P : Set (Fin r)) (phi : Nat → Nat)
    (hLow : ∀ x, x < q → phi x = x)
    (a : Fin r) (j : Nat) (hj : j < N) (hq : q ≤ N)
    (hTop : phi (q+a.val) = j) :
    RelationalPrefixType.ofAgeModel
      (continuationPullback Q.ageModel q r P phi) q (q+a.val) =
        (Q.ordinaryType j hj q hq).lReduct := by
  have hIndex (x : Nat) (hx : x < q) : x < N := lt_of_lt_of_le hx hq
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    cases x <;> cases y <;>
      simp [RelationalPrefixType.ofAgeModel,continuationPullback,
        PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
        typeAgeIndex,prefixVertexIndex,ordinaryTypeCoordinate,
        hTop,hLow,hIndex,hj]
  · intro x t
    cases x <;>
      simp [RelationalPrefixType.ofAgeModel,continuationPullback,
        PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
        typeAgeIndex,prefixVertexIndex,ordinaryTypeCoordinate,
        hTop,hLow,hIndex,hj]
  · intro x t
    cases x <;>
      simp [RelationalPrefixType.ofAgeModel,continuationPullback,
        PartialTypeWithE.ageModel,PartialTypeWithE.ordinaryType,
        typeAgeIndex,prefixVertexIndex,ordinaryTypeCoordinate,
        hTop,hLow,hIndex,hj]

private theorem shapeMap_labelled_age_exists
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {n q r : Nat} (hn : 0 < n)
    (hCut : kptShapeLevelMap family F n = q)
    (P : Set (Fin r)) (hNonempty : P.Nonempty)
    (T : Fin r → PartialTypeWithE n db du dd)
    (hAd : ∀ a : Fin r, a ∈ P →
      IsAdmissibleRawType family (⟨n,T a⟩ : RawPartialTypeNode db du dd))
    (hComp : ∀ a b : Fin r, a ∈ P → b ∈ P →
      SameOrdinaryAtCut (T a) (T b))
    (W : AgeTestModel db du dd)
    (hWCarrier : ∀ x, x ∈ W.carrier ↔
      x < n ∨ ∃ a : Fin r, a ∈ P ∧ x = n+a.val)
    (hSource : ∀ a : Fin r, a ∈ P →
      RelationalPrefixType.ofAgeModel W n (n+a.val) = (T a).lReduct)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids W) :
    ∃ V : AgeTestModel db du dd,
      (∀ x, x ∈ V.carrier ↔
        x < q ∨ ∃ a : Fin r, a ∈ P ∧ x = q+a.val) ∧
      (∀ (a : Fin r) (ha : a ∈ P),
        (⟨q,RelationalPrefixType.ofAgeModel V q (q+a.val)⟩ :
          RawRelationalTypeNode db du dd) =
            (F (⟨⟨n,T a⟩,hAd a ha⟩ : AdmissibleKptNode family)).relationalNode) ∧
      SameUpperL W V n q r P ∧
      (∀ bad, bad ∈ family → bad.Avoids V) := by
  classical
  obtain ⟨a0,ha0⟩ := hNonempty
  let A := W.fillNeutralCarrier (n+r)
  have hWLow (x : Nat) (hx : x < n) : x ∈ W.carrier :=
    (hWCarrier x).2 (Or.inl hx)
  have hWUpper (a : Fin r) (ha : a ∈ P) : n+a.val ∈ W.carrier :=
    (hWCarrier _).2 (Or.inr ⟨a,ha,rfl⟩)
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A := by
    intro bad hbad
    exact bad.avoids_fillNeutralCarrier W (n+r) (by
      intro x hx
      rcases (hWCarrier x).1 hx with hx | ⟨a,ha,rfl⟩
      · omega
      · exact Nat.add_lt_add_left a.isLt n) (hAvoid bad hbad)
  let selected (j : Nat) : Prop :=
    ∃ a : Fin r, a ∈ P ∧ j = n+a.val
  let types (j : Nat) : PartialTypeWithE n db du dd :=
    if h : j-n < r then T ⟨j-n,h⟩ else T a0
  have hTypes (a : Fin r) : types (n+a.val) = T a := by
    have hBound : n+a.val-n < r := by omega
    have hFin : (⟨n+a.val-n,hBound⟩ : Fin r) = a := Fin.ext (by
      change n+a.val-n = a.val
      omega)
    simp only [types,dif_pos hBound,hFin]
  have hInitial : ∀ (x y : Nat) (hx : x < n) (hy : y < n)
      (t : Fin db), A.binary x y t =
        (T a0).lReduct.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t := by
    intro x y hx hy t
    rw [show A.binary x y t = W.binary x y t from
      W.fillNeutralCarrier_old_binary (n+r) x y (hWLow x hx) (hWLow y hy) t]
    exact congrArg (fun R : RelationalPrefixType n db du dd =>
      R.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t) (hSource a0 ha0)
  obtain ⟨B,hAvoidB,hSize,hL,hSelected⟩ :=
    compatibleSelectedTypes_joint_padded_with_L family (T a0) (hAd a0 ha0)
      A (n+r) (by omega) (by intro x; rfl) hAvoidA hInitial selected types
      (by
        intro j _ _ hsel
        rcases hsel with ⟨a,ha,rfl⟩
        simpa only [hTypes a] using hAd a ha)
      (by
        intro j _ _ hsel
        rcases hsel with ⟨a,ha,rfl⟩
        simpa only [hTypes a] using hComp a0 a ha0 ha)
      (by
        intro j _ _ hsel
        rcases hsel with ⟨a,ha,rfl⟩
        rw [hTypes a]
        exact (fillNeutralCarrier_type W (n+r) n (n+a.val)
          hWLow (hWUpper a ha)).trans (hSource a ha))
  let u := NonedgePadding.socleCapNode family B hAvoidB
  let lambda := kptShapeLevelMap family F
  let phi : Nat → Nat := fun x =>
    if x < q then x else lambda (NonedgePadding.address n (n+(x-q)))
  let V := continuationPullback (F u).1.2.ageModel q r P phi
  have hVCarrier : ∀ x, x ∈ V.carrier ↔
      x < q ∨ ∃ a : Fin r, a ∈ P ∧ x = q+a.val := by
    intro x
    rfl
  have hPhiLow (x : Nat) (hx : x < q) : phi x = x := by
    simp [phi,hx]
  have hPhiUpper (a : Fin r) :
      phi (q+a.val) = lambda (NonedgePadding.address n (n+a.val)) := by
    simp [phi]
  have hFullType (a : Fin r) (ha : a ∈ P) :
      B.partialTypeAt n (NonedgePadding.address n (n+a.val)) = T a := by
    simpa only [hTypes a] using hSelected (n+a.val)
      (by omega) (by omega) ⟨a,ha,rfl⟩
  have hTransport (a : Fin r) (ha : a ∈ P) :
      ∃ (hj : kptShapeLevelMap family F
          (NonedgePadding.address n (n+a.val)) < (F u).1.1)
        (hq : q ≤ (F u).1.1),
        (⟨q,((F u).1.2.ordinaryType
          (lambda (NonedgePadding.address n (n+a.val))) hj q hq).lReduct⟩ :
          RawRelationalTypeNode db du dd) =
            (F (⟨⟨n,T a⟩,hAd a ha⟩ : AdmissibleKptNode family)).relationalNode := by
    have hj : NonedgePadding.address n (n+a.val) < B.size := by
      rw [hSize]
      exact NonedgePadding.address_lt_size n (n+r) (n+a.val) (by omega)
    have hnj : n ≤ NonedgePadding.address n (n+a.val) := by
      simp only [NonedgePadding.address]
      split_ifs <;> omega
    obtain ⟨hAddress,hSocle,hType⟩ := shapeMap_transports_padded_selected_type
      family F B hAvoidB (NonedgePadding.address n (n+a.val)) hn hnj hj
      (T a) (hAd a ha) (hFullType a ha)
    have hLevel : q =
        (F (⟨⟨n,T a⟩,hAd a ha⟩ : AdmissibleKptNode family)).1.1 :=
      hCut.symm.trans (kptShapeLevelMap_eq family F
        (⟨⟨n,T a⟩,hAd a ha⟩ : AdmissibleKptNode family))
    obtain ⟨hq,hRecord⟩ := ordinary_type_relational_sigma (F u).1.2 _ hAddress
      (F (⟨⟨n,T a⟩,hAd a ha⟩ : AdmissibleKptNode family))
      hSocle hType hLevel
    exact ⟨hAddress,hq,hRecord⟩
  have hImageUpper (a : Fin r) (ha : a ∈ P) :
      ∃ (hj : lambda (NonedgePadding.address n (n+a.val)) < (F u).1.1)
        (hq : q ≤ (F u).1.1),
        ((F u).1.2.ordinaryType
          (lambda (NonedgePadding.address n (n+a.val))) hj q hq).lReduct =
            RelationalPrefixType.ofAgeModel V q (q+a.val) := by
    obtain ⟨hj,hq,_⟩ := hTransport a ha
    exact ⟨hj,hq,(continuationPullback_type (F u).1.2 P phi hPhiLow
      a _ hj hq (hPhiUpper a)).symm⟩
  have hTarget (a : Fin r) (ha : a ∈ P) :
      (⟨q,RelationalPrefixType.ofAgeModel V q (q+a.val)⟩ :
        RawRelationalTypeNode db du dd) =
          (F (⟨⟨n,T a⟩,hAd a ha⟩ : AdmissibleKptNode family)).relationalNode := by
    obtain ⟨hj,hq,hRecord⟩ := hTransport a ha
    rw [show RelationalPrefixType.ofAgeModel V q (q+a.val) =
      ((F u).1.2.ordinaryType _ hj q hq).lReduct from
        continuationPullback_type (F u).1.2 P phi hPhiLow
          a _ hj hq (hPhiUpper a)]
    exact hRecord
  have hUpperL : SameUpperL W V n q r P := by
    refine ⟨?_,?_,?_⟩
    · intro a b ha hb t
      change W.binary (n+a.val) (n+b.val) t =
        (F u).1.2.ageModel.binary (phi (q+a.val)) (phi (q+b.val)) t
      rw [hPhiUpper,hPhiUpper]
      obtain ⟨hi,hj,hAtom⟩ := shapeMap_padded_cap_real_binary
        family F A B hAvoidB n (n+r) hSize hL
        (n+a.val) (n+b.val) (by omega) (by omega) t
      exact ((hAtom.trans (W.fillNeutralCarrier_old_binary (n+r) _ _
        (hWUpper a ha) (hWUpper b hb) t))).symm
    · intro a ha t
      change W.unary (n+a.val) t = (F u).1.2.ageModel.unary (phi (q+a.val)) t
      rw [hPhiUpper]
      obtain ⟨hi,hUnary,hDiagonal⟩ := shapeMap_padded_cap_real_singletons
        family F A B hAvoidB n (n+r) hSize hL (n+a.val) (by omega)
      exact ((hUnary t).trans (W.fillNeutralCarrier_old_unary (n+r) _
        (hWUpper a ha) t)).symm
    · intro a ha t
      change W.diagonal (n+a.val) t =
        (F u).1.2.ageModel.diagonal (phi (q+a.val)) t
      rw [hPhiUpper]
      obtain ⟨hi,hUnary,hDiagonal⟩ := shapeMap_padded_cap_real_singletons
        family F A B hAvoidB n (n+r) hSize hL (n+a.val) (by omega)
      exact ((hDiagonal t).trans (W.fillNeutralCarrier_old_diagonal (n+r) _
        (hWUpper a ha) t)).symm
  obtain ⟨H⟩ := continuation_embeds_in_image_type (F u).1.2 V P
    (kptShapeLevelMap family F) (kptShapeLevelMap_strictMono family F)
    hCut hVCarrier ⟨a0,ha0⟩ hImageUpper (by
      intro a b ha hb t
      change (F u).1.2.ageModel.binary _ _ t =
        (F u).1.2.ageModel.binary (phi (q+a.val)) (phi (q+b.val)) t
      rw [hPhiUpper,hPhiUpper])
  exact ⟨V,hVCarrier,hTarget,hUpperL,H.preserves_avoidance family
    ((F u).1.2.ageModel_avoids family (F u).2)⟩

private def recordAtLevel (u : RawPartialTypeNode db du dd)
    {n : Nat} (h : u.1 = n) : PartialTypeWithE n db du dd := h ▸ u.2

private theorem recordAtLevel_raw (u : RawPartialTypeNode db du dd)
    {n : Nat} (h : u.1 = n) :
    (⟨n,recordAtLevel u h⟩ : RawPartialTypeNode db du dd) = u := by
  cases u with
  | mk m T => cases h; rfl

private theorem same_socle_of_profile_raw
    {A : FiniteTypeBase family} {n : Nat}
    (u : TypeProfile A) (T : PartialTypeWithE n db du dd)
    (hRaw : (⟨n,T⟩ : RawPartialTypeNode db du dd) = u.1.1) :
    SameOrdinaryAtCut T (A.str.partialTypeAt n 0) := by
  have hLevel : n = u.level := congrArg Sigma.fst hRaw
  subst n
  have hT : T = u.1.1.2 := eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  rw [hT]
  exact u.same_socle

private theorem socle_atoms_of_relational_sigma
    (B : FiniteTypeBase family) (u : AdmissibleKptNode family)
    (W : AgeTestModel db du dd) (q w : Nat)
    (hSigma : (⟨q,RelationalPrefixType.ofAgeModel W q w⟩ :
      RawRelationalTypeNode db du dd) = u.relationalNode)
    (hSocle : SameOrdinaryAtCut u.1.2 (B.str.partialTypeAt u.1.1 0)) :
    (∀ x y : Fin q, ∀ t : Fin db,
      W.binary x.val y.val t = B.str.L.binary x.val y.val t) ∧
    (∀ x : Fin q, ∀ t : Fin du,
      W.unary x.val t = B.str.L.unary x.val t) ∧
    (∀ x : Fin q, ∀ t : Fin dd,
      W.diagonal x.val t = B.str.L.diagonal x.val t) := by
  have hLevel : q = u.1.1 := congrArg Sigma.fst hSigma
  subst q
  have hT : RelationalPrefixType.ofAgeModel W u.1.1 w = u.1.2.lReduct :=
    eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
  refine ⟨?_,?_,?_⟩
  · intro x y t
    exact (congrArg (fun R : RelationalPrefixType u.1.1 db du dd =>
      R.binary (some x) (some y) t) hT).trans (hSocle.1 x y t)
  · intro x t
    exact (congrArg (fun R : RelationalPrefixType u.1.1 db du dd =>
      R.unary (some x) t) hT).trans (hSocle.2.1 x t)
  · intro x t
    exact (congrArg (fun R : RelationalPrefixType u.1.1 db du dd =>
      R.diagonal (some x) t) hT).trans (hSocle.2.2.1 x t)

/-- Restricting a genuine global shape map to a coherent full finite
profile preserves every allowed finite labelled L-continuation. The
extension witness is used only through its actual finite values. -/
theorem CoherentTypeProfileMap.preservesAge_of_shapeMap_restriction
    {A B : FiniteTypeBase family}
    (h : CoherentTypeProfileMap A B)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hAgree : ∀ u : TypeProfile A, F u.1 = h u) :
    h.PreservesAge := by
  classical
  intro i r P labels W hW hAvoid
  have hLabelLevel (a : Fin r) (ha : a ∈ P) :
      (labels a).level = i.val :=
    (congrArg Sigma.fst (hW.upper_types a ha)).symm
  by_cases hn : i.val = 0
  · have hi : i = ⟨0,Nat.zero_lt_succ A.size⟩ := Fin.ext hn
    have hq : (h.cutMap i).val = 0 := by rw [hi,h.cut_zero]
    refine ⟨W,?_,?_,hAvoid⟩
    · refine ⟨?_,?_,?_,?_,?_⟩
      · intro x
        simpa only [hn,hq] using hW.carrier x
      · intro x y t
        have hx := x.isLt
        omega
      · intro x t
        have hx := x.isLt
        omega
      · intro x t
        have hx := x.isLt
        omega
      · intro a ha
        rw [h.root_fixed (labels a) ((hLabelLevel a ha).trans hn)]
        exact (congrArg (fun k : Nat =>
          (⟨k,RelationalPrefixType.ofAgeModel W k (k+a.val)⟩ :
            RawRelationalTypeNode db du dd)) (hq.trans hn.symm)).trans
              (hW.upper_types a ha)
    · refine ⟨?_,?_,?_⟩ <;> intros <;> simp only [hn,hq]
  by_cases hP : P.Nonempty
  · obtain ⟨a0,ha0⟩ := hP
    let T : Fin r → PartialTypeWithE i.val db du dd := fun a =>
      if ha : a ∈ P then recordAtLevel (labels a).1.1 (hLabelLevel a ha)
      else recordAtLevel (labels a0).1.1 (hLabelLevel a0 ha0)
    have hRaw (a : Fin r) (ha : a ∈ P) :
        (⟨i.val,T a⟩ : RawPartialTypeNode db du dd) = (labels a).1.1 := by
      simp only [T,dif_pos ha]
      exact recordAtLevel_raw _ _
    have hAd (a : Fin r) (ha : a ∈ P) :
        IsAdmissibleRawType family (⟨i.val,T a⟩ : RawPartialTypeNode db du dd) := by
      rw [hRaw a ha]
      exact (labels a).1.2
    have hNode (a : Fin r) (ha : a ∈ P) :
        (⟨⟨i.val,T a⟩,hAd a ha⟩ : AdmissibleKptNode family) = (labels a).1 :=
      Subtype.ext (hRaw a ha)
    have hComp (a b : Fin r) (ha : a ∈ P) (hb : b ∈ P) :
        SameOrdinaryAtCut (T a) (T b) :=
      sameOrdinaryAtCut_trans
        (same_socle_of_profile_raw (labels a) (T a) (hRaw a ha))
        (sameOrdinaryAtCut_symm
          (same_socle_of_profile_raw (labels b) (T b) (hRaw b hb)))
    have hSource (a : Fin r) (ha : a ∈ P) :
        RelationalPrefixType.ofAgeModel W i.val (i.val+a.val) = (T a).lReduct := by
      have hSigma := hW.upper_types a ha
      rw [←hNode a ha] at hSigma
      exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
    have hCut : kptShapeLevelMap family F i.val = (h.cutMap i).val := by
      have hLabelCut : (labels a0).cut = i := Fin.ext (hLabelLevel a0 ha0)
      calc
        kptShapeLevelMap family F i.val =
            kptShapeLevelMap family F (labels a0).level :=
          congrArg _ (hLabelLevel a0 ha0).symm
        _ = (F (labels a0).1).1.1 := kptShapeLevelMap_eq family F (labels a0).1
        _ = (h (labels a0)).1.1 := congrArg (fun u => u.1.1) (hAgree (labels a0))
        _ = (h.cutMap i).val := by rw [h.level_eq,hLabelCut]
    obtain ⟨V,hCarrier,hTarget,hUpperL,hAvoidV⟩ :=
      shapeMap_labelled_age_exists F (n := i.val) (q := (h.cutMap i).val)
        (by omega) hCut P ⟨a0,ha0⟩ T hAd hComp
        W hW.carrier hSource hAvoid
    have hTarget' (a : Fin r) (ha : a ∈ P) :
        (⟨(h.cutMap i).val,
          RelationalPrefixType.ofAgeModel V (h.cutMap i).val
            ((h.cutMap i).val+a.val)⟩ : RawRelationalTypeNode db du dd) =
          (h (labels a)).relationalNode := by
      simpa only [hNode a ha,hAgree (labels a)] using hTarget a ha
    obtain ⟨hBinary,hUnary,hDiagonal⟩ := socle_atoms_of_relational_sigma B
      (h (labels a0)) V (h.cutMap i).val ((h.cutMap i).val+a0.val)
      (hTarget' a0 ha0) (h.maps_socle (labels a0))
    exact ⟨V,⟨hCarrier,hBinary,hUnary,hDiagonal,hTarget'⟩,hUpperL,hAvoidV⟩
  · have hEmpty (a : Fin r) : a ∉ P := fun ha => hP ⟨a,ha⟩
    let V := B.str.L.restrictCarrier (fun x => x < (h.cutMap i).val)
    refine ⟨V,?_,?_,?_⟩
    · refine ⟨?_,?_,?_,?_,?_⟩
      · intro x
        change (x ∈ B.str.L.carrier ∧ x < (h.cutMap i).val) ↔ _
        constructor
        · intro hx
          exact Or.inl hx.2
        · rintro (hx | ⟨a,ha,hx⟩)
          · exact ⟨(B.str.carrier_iff x).2 (by
              change x < B.size
              have hBound := (h.cutMap i).isLt
              omega),hx⟩
          · exact (hEmpty a ha).elim
      · intros; rfl
      · intros; rfl
      · intros; rfl
      · intro a ha
        exact (hEmpty a ha).elim
    · refine ⟨?_,?_,?_⟩
      · intro a b ha hb t
        exact (hEmpty a ha).elim
      · intro a ha t
        exact (hEmpty a ha).elim
      · intro a ha t
        exact (hEmpty a ha).elim
    · let H : V.InducedEmbeddingOnCarrier B.str.L := {
        toFun := id
        order := fun _ _ _ _ hxy => hxy
        inside := fun _ hx => hx.1
        binary := by intros; rfl
        unary := by intros; rfl
        diagonal := by intros; rfl }
      exact H.preserves_avoidance family B.avoids

end SuccessorTree.V10
