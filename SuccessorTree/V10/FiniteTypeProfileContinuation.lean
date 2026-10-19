import SuccessorTree.V10.FiniteTypeProfile
import SuccessorTree.V10.M2ShapeMapCompatReflection
import SuccessorTree.V10.M2SparsePullbackAge

/-!
# Finite labelled continuations and induced restriction

The elementary constructions here keep a finite ordered upper carrier and
reindex only its initial socle. They are used both to interpret the intrinsic
continuation condition and to discharge the existing boring-extension age
test. No auxiliary E relation is placed on an age witness.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- Restrict the ordinary coordinates of a complete relational type. -/
def RelationalPrefixType.reindexOrdinary {n m : Nat}
    (Q : RelationalPrefixType m db du dd) (rho : Fin n → Fin m) :
    RelationalPrefixType n db du dd where
  binary := fun x y t => Q.binary (x.map rho) (y.map rho) t
  unary := fun x t => Q.unary (x.map rho) t
  diagonal := fun x t => Q.diagonal (x.map rho) t

@[simp] theorem PartialTypeWithE.reindexOrdinary_lReduct {n m : Nat}
    (Q : PartialTypeWithE m db du dd) (rho : Fin n → Fin m) :
    (Q.reindexOrdinary rho).lReduct = Q.lReduct.reindexOrdinary rho := rfl

/-- Reindex an initial socle and retain the increasing enumeration of the
upper vertices. The formula also gives harmless values at unused positions. -/
def continuationIndex {n m : Nat} (rho : Fin n → Fin m) (x : Nat) : Nat :=
  if hx : x < n then (rho ⟨x, hx⟩).val else m + (x - n)

@[simp] theorem continuationIndex_low {n m : Nat}
    (rho : Fin n → Fin m) (x : Fin n) :
    continuationIndex rho x.val = (rho x).val := by
  simp [continuationIndex, x.isLt]

@[simp] theorem continuationIndex_upper {n m : Nat}
    (rho : Fin n → Fin m) (x : Nat) :
    continuationIndex rho (n + x) = m + x := by
  simp [continuationIndex]

theorem continuationIndex_strictMono {n m : Nat}
    (rho : Fin n → Fin m) (hMono : StrictMono rho) :
    StrictMono (continuationIndex rho) := by
  intro x y hxy
  by_cases hy : y < n
  · have hx : x < n := by omega
    simpa only [continuationIndex, dif_pos hx, dif_pos hy, Fin.lt_def] using
      hMono (show (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ from hxy)
  · by_cases hx : x < n
    · simp only [continuationIndex, dif_pos hx, dif_neg hy]
      have hBound := (rho ⟨x, hx⟩).isLt
      omega
    · simp only [continuationIndex, dif_neg hx, dif_neg hy]
      omega

theorem continuationIndex_typeCoordinate {n m : Nat}
    (rho : Fin n → Fin m) (x : Nat) (a : Option (Fin n)) :
    continuationIndex rho (prefixVertexIndex (n + x) a) =
      prefixVertexIndex (m + x) (a.map rho) := by
  cases a with
  | none => exact continuationIndex_upper rho x
  | some a => exact continuationIndex_low rho a

/-- The same finite upper carrier, with a different initial socle. -/
def AgeTestModel.continuationPullback {n m r : Nat}
    (W : AgeTestModel db du dd) (rho : Fin n → Fin m)
    (P : Set (Fin r)) : AgeTestModel db du dd where
  carrier := {x | x < n ∨ ∃ a : Fin r, a ∈ P ∧ x = n + a.val}
  binary := fun x y t => W.binary (continuationIndex rho x) (continuationIndex rho y) t
  unary := fun x t => W.unary (continuationIndex rho x) t
  diagonal := fun x t => W.diagonal (continuationIndex rho x) t

/-- All complete types in the pullback are the expected ordinary-coordinate
restrictions, including the distinguished singleton. -/
theorem AgeTestModel.continuationPullback_type {n m r : Nat}
    (W : AgeTestModel db du dd) (rho : Fin n → Fin m)
    (P : Set (Fin r)) (a : Fin r) :
    RelationalPrefixType.ofAgeModel (W.continuationPullback rho P) n (n + a.val) =
      (RelationalPrefixType.ofAgeModel W m (m + a.val)).reindexOrdinary rho := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    change W.binary (continuationIndex rho (prefixVertexIndex (n + a.val) x))
        (continuationIndex rho (prefixVertexIndex (n + a.val) y)) t = _
    rw [continuationIndex_typeCoordinate, continuationIndex_typeCoordinate]
    rfl
  · intro x t
    change W.unary (continuationIndex rho (prefixVertexIndex (n + a.val) x)) t = _
    rw [continuationIndex_typeCoordinate]
    rfl
  · intro x t
    change W.diagonal (continuationIndex rho (prefixVertexIndex (n + a.val) x)) t = _
    rw [continuationIndex_typeCoordinate]
    rfl

theorem AgeTestModel.continuationPullback_sameUpper {n m r : Nat}
    (W : AgeTestModel db du dd) (rho : Fin n → Fin m)
    (P : Set (Fin r)) :
    SameUpperL (W.continuationPullback rho P) W n m r P := by
  constructor
  · intro x y hx hy t
    change W.binary (continuationIndex rho (n + x.val))
      (continuationIndex rho (n + y.val)) t = _
    rw [continuationIndex_upper, continuationIndex_upper]
  · intro x hx t
    change W.unary (continuationIndex rho (n + x.val)) t = _
    rw [continuationIndex_upper]
  · intro x hx t
    change W.diagonal (continuationIndex rho (n + x.val)) t = _
    rw [continuationIndex_upper]

/-- An actual induced embedding into the original witness, restricted to
the selected ordinary coordinates and the existing upper carrier. -/
def AgeTestModel.continuationPullback_induced {n m r : Nat}
    (W : AgeTestModel db du dd) (rho : Fin n → Fin m)
    (P : Set (Fin r)) (hMono : StrictMono rho)
    (hLow : ∀ x : Fin n, (rho x).val ∈ W.carrier)
    (hUpper : ∀ x : Fin r, x ∈ P → m + x.val ∈ W.carrier) :
    (W.continuationPullback rho P).InducedEmbeddingOnCarrier W where
  toFun := continuationIndex rho
  order := fun x y _ _ hxy => continuationIndex_strictMono rho hMono hxy
  inside := by
    intro x hx
    rcases hx with hx | ⟨a, ha, rfl⟩
    · simpa only [continuationIndex, dif_pos hx] using hLow ⟨x, hx⟩
    · simpa only [continuationIndex_upper] using hUpper a ha
  binary := fun _ _ _ _ _ _ => rfl
  unary := fun _ _ _ => rfl
  diagonal := fun _ _ _ => rfl

namespace ProfileContinuation

variable {A : FiniteTypeBase family} {i : Fin (A.size + 1)}
variable {r : Nat} {P : Set (Fin r)}
variable {labels : Fin r → AdmissibleKptNode family}
variable {W : AgeTestModel db du dd}

theorem bounded (h : ProfileContinuation A i r P labels W) : W.BoundedCarrier := by
  refine ⟨i.val + r, ?_⟩
  intro x hx
  rcases (h.carrier x).1 hx with hx | ⟨a, ha, rfl⟩
  · omega
  · omega

theorem label_level (h : ProfileContinuation A i r P labels W)
    (a : Fin r) (ha : a ∈ P) : (labels a).1.1 = i.val :=
  (congrArg Sigma.fst (h.upper_types a ha)).symm

theorem initial_mem (h : ProfileContinuation A i r P labels W)
    (x : Nat) (hx : x < i.val) : x ∈ W.carrier :=
  (h.carrier x).2 (Or.inl hx)

theorem upper_mem (h : ProfileContinuation A i r P labels W)
    (a : Fin r) (ha : a ∈ P) : i.val + a.val ∈ W.carrier :=
  (h.carrier _).2 (Or.inr ⟨a, ha, rfl⟩)

private theorem relational_restrict_of_sigma_eq
    {n : Nat} (Q : RelationalPrefixType n db du dd)
    (U : RawRelationalTypeNode db du dd)
    (h : (⟨n, Q⟩ : RawRelationalTypeNode db du dd) = U)
    (k : Nat) (hk : k ≤ n) :
    Q.restrict hk = U.2.restrict (hk.trans (congrArg Sigma.fst h).le) := by
  cases h
  rfl

/-- A continuation realizes every shorter prefix of each complete label,
without changing the address of its distinguished upper vertex. -/
theorem upper_restrict (h : ProfileContinuation A i r P labels W)
    (a : Fin r) (ha : a ∈ P) (k : Nat) (hk : k ≤ i.val) :
    RelationalPrefixType.ofAgeModel W k (i.val + a.val) =
      ((labels a).1.2.restrict
        (hk.trans (h.label_level a ha).symm.le)).lReduct := by
  have hRec := relational_restrict_of_sigma_eq
    (RelationalPrefixType.ofAgeModel W i.val (i.val + a.val))
    (labels a).relationalNode (h.upper_types a ha) k hk
  calc
    RelationalPrefixType.ofAgeModel W k (i.val + a.val) =
        (RelationalPrefixType.ofAgeModel W i.val (i.val + a.val)).restrict hk :=
      (RelationalPrefixType.ofAgeModel_restrict W k i.val (i.val + a.val) hk).symm
    _ = _ := hRec

end ProfileContinuation

namespace SameUpperL

theorem symm {W V : AgeTestModel db du dd} {i j r : Nat} {P : Set (Fin r)}
    (h : SameUpperL W V i j r P) : SameUpperL V W j i r P :=
  ⟨fun x y hx hy t => (h.binary x y hx hy t).symm,
    fun x hx t => (h.unary x hx t).symm,
    fun x hx t => (h.diagonal x hx t).symm⟩

theorem trans {W V U : AgeTestModel db du dd} {i j k r : Nat} {P : Set (Fin r)}
    (h : SameUpperL W V i j r P) (g : SameUpperL V U j k r P) :
    SameUpperL W U i k r P :=
  ⟨fun x y hx hy t => (h.binary x y hx hy t).trans (g.binary x y hx hy t),
    fun x hx t => (h.unary x hx t).trans (g.unary x hx t),
    fun x hx t => (h.diagonal x hx t).trans (g.diagonal x hx t)⟩

end SameUpperL

/-- Complete upper types determine every atom meeting the initial socle.
Together with the upper binary structure they determine an induced embedding
along a prescribed increasing map of ordinary coordinates. -/
theorem continuation_induced_of_types
    {n m r : Nat} (W V : AgeTestModel db du dd) (P : Set (Fin r))
    (rho : Fin n → Fin m) (hMono : StrictMono rho) (hNonempty : P.Nonempty)
    (hW : ∀ x, x ∈ W.carrier ↔ x < n ∨ ∃ a : Fin r, a ∈ P ∧ x = n + a.val)
    (hV : ∀ x, x ∈ V.carrier ↔ x < m ∨ ∃ a : Fin r, a ∈ P ∧ x = m + a.val)
    (hType : ∀ a : Fin r, a ∈ P →
      RelationalPrefixType.ofAgeModel W n (n + a.val) =
        (RelationalPrefixType.ofAgeModel V m (m + a.val)).reindexOrdinary rho)
    (hBinary : ∀ a b : Fin r, a ∈ P → b ∈ P → ∀ t : Fin db,
      W.binary (n + a.val) (n + b.val) t =
        V.binary (m + a.val) (m + b.val) t) :
    Nonempty (W.InducedEmbeddingOnCarrier V) := by
  obtain ⟨a0, ha0⟩ := hNonempty
  refine ⟨{
    toFun := continuationIndex rho
    order := fun x y _ _ hxy => continuationIndex_strictMono rho hMono hxy
    inside := ?_
    binary := ?_
    unary := ?_
    diagonal := ?_ }⟩
  · intro x hx
    rcases (hW x).1 hx with hx | ⟨a, ha, rfl⟩
    · rw [show continuationIndex rho x = (rho ⟨x, hx⟩).val from
        continuationIndex_low rho ⟨x, hx⟩]
      exact (hV _).2 (Or.inl (rho ⟨x, hx⟩).isLt)
    · rw [continuationIndex_upper]
      exact (hV _).2 (Or.inr ⟨a, ha, rfl⟩)
  · intro x y hx hy hxy t
    rcases (hW x).1 hx with hx | ⟨a, ha, rfl⟩
    · rcases (hW y).1 hy with hy | ⟨b, hb, rfl⟩
      · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
          Q.binary (some ⟨x, hx⟩) (some ⟨y, hy⟩) t) (hType a0 ha0)
        simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
          prefixVertexIndex, continuationIndex, hx, hy] using hAtom.symm
      · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
          Q.binary (some ⟨x, hx⟩) none t) (hType b hb)
        simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
          prefixVertexIndex, continuationIndex, hx] using hAtom.symm
    · rcases (hW y).1 hy with hy | ⟨b, hb, rfl⟩
      · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
          Q.binary none (some ⟨y, hy⟩) t) (hType a ha)
        simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
          prefixVertexIndex, continuationIndex, hy] using hAtom.symm
      · simpa only [continuationIndex_upper] using (hBinary a b ha hb t).symm
  · intro x hx t
    rcases (hW x).1 hx with hx | ⟨a, ha, rfl⟩
    · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
        Q.unary (some ⟨x, hx⟩) t) (hType a0 ha0)
      simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
        prefixVertexIndex, continuationIndex, hx] using hAtom.symm
    · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
        Q.unary none t) (hType a ha)
      simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
        prefixVertexIndex, continuationIndex] using hAtom.symm
  · intro x hx t
    rcases (hW x).1 hx with hx | ⟨a, ha, rfl⟩
    · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
        Q.diagonal (some ⟨x, hx⟩) t) (hType a0 ha0)
      simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
        prefixVertexIndex, continuationIndex, hx] using hAtom.symm
    · have hAtom := congrArg (fun Q : RelationalPrefixType n db du dd =>
        Q.diagonal none t) (hType a ha)
      simpa [RelationalPrefixType.ofAgeModel, RelationalPrefixType.reindexOrdinary,
        prefixVertexIndex, continuationIndex] using hAtom.symm

end SuccessorTree.V10
