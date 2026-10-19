import SuccessorTree.V10.FiniteTypeProfileCap
import SuccessorTree.V10.M2ShapeMapCompatReflection

/-!
# Local recovery for intrinsic finite type-profile maps

The finite domain is closed under prefixes and actual canonical parameters.
Consequently the weak successor law recovers every retained L+ atom, including
negative atoms. No extension to a global shape map and no age hypothesis are
used in these results.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- A canonical E column determines the actual free cut of its ordinary
vertex in any compatible finite base. -/
theorem sameOrdinaryAtCut_freeLevel_eq_of_validNewColumn
    (A : EnumeratedPartialStructure db du dd) {ell : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (hSocle : SameOrdinaryAtCut Q (A.partialTypeAt (ell + 1) 0))
    (f : Nat) (hf : f ≤ ell) (hValid : ValidNewOrdinaryColumn Q f) :
    A.freeLevel ell = f := by
  have hColumn (i : Fin ell) : A.E i.val ell = decide (i.val < f) :=
    (hSocle.2.2.2 i.castSucc (Fin.last ell)).symm.trans (hValid.oldToNewE i)
  have hActual := A.freeLevel_le ell
  apply Nat.le_antisymm
  · by_contra hNot
    have hLess : f < A.freeLevel ell := by omega
    have hTrue : A.E f ell = true := (A.E_iff_freeLevel f ell).2 hLess
    have hFalse : A.E f ell = false :=
      (hColumn ⟨f, by omega⟩).trans (by simp)
    rw [hTrue] at hFalse
    contradiction
  · by_contra hNot
    have hLess : A.freeLevel ell < f := by omega
    have hTrue : A.E (A.freeLevel ell) ell = true :=
      (hColumn ⟨A.freeLevel ell, by omega⟩).trans (by simp [hLess])
    have hFalse := A.freeLevel_firstMissing ell
    rw [hTrue] at hFalse
    contradiction

namespace TypeProfile

variable {A : FiniteTypeBase family}

/-- Every initial prefix remains in the full compatible profile. -/
theorem mem_of_le (u : TypeProfile A) {v : AdmissibleKptNode family}
    (hvu : v ≤ u.1) : v ∈ A.profile := by
  have hv : v.1.1 ≤ u.level := hvu.1
  refine ⟨hv.trans u.level_le_size, ?_⟩
  rw [hvu.2]
  exact ⟨fun i j t => u.same_socle.1
      ⟨i.val, lt_of_lt_of_le i.isLt hv⟩
      ⟨j.val, lt_of_lt_of_le j.isLt hv⟩ t,
    fun i t => u.same_socle.2.1
      ⟨i.val, lt_of_lt_of_le i.isLt hv⟩ t,
    fun i t => u.same_socle.2.2.1
      ⟨i.val, lt_of_lt_of_le i.isLt hv⟩ t,
    fun i j => u.same_socle.2.2.2
      ⟨i.val, lt_of_lt_of_le i.isLt hv⟩
      ⟨j.val, lt_of_lt_of_le j.isLt hv⟩⟩

/-- A profile prefix, with its literal restricted record. -/
abbrev ancestor (u : TypeProfile A) (n : Nat) (hn : n ≤ u.level) :
    TypeProfile A :=
  ⟨admissibleKptAncestor u.1 n hn,
    u.mem_of_le (admissibleKptAncestor_le u.1 n hn)⟩

@[simp] theorem ancestor_level (u : TypeProfile A) (n : Nat)
    (hn : n ≤ u.level) : (u.ancestor n hn).level = n := rfl

theorem ancestor_le (u : TypeProfile A) (n : Nat) (hn : n ≤ u.level) :
    (u.ancestor n hn).1 ≤ u.1 :=
  admissibleKptAncestor_le u.1 n hn

theorem ancestor_val (u : TypeProfile A) (n : Nat) (hn : n ≤ u.level) :
    (u.ancestor n hn).1 = LevelTree.ancestor u.1 n hn :=
  (admissibleKpt_levelTree_ancestor_eq u.1 n hn).symm

/-- An actual canonical parameter inherits the same earlier ordinary socle.
The distinguished vertex of the parameter is an ordinary vertex of the
upper type, so it introduces no additional domain condition. -/
theorem parameter_mem (u : TypeProfile A)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) (hBelow : b ≤ u.1)
    (v : AdmissibleKptNode family) (hv : v ∈ p) : v ∈ A.profile := by
  obtain ⟨hj, hf, hRaw⟩ :=
    canonicalKptStep_parameter_in_upper family hStep hBelow v hv
  have hRecord : v.1.2 = u.1.1.2.ordinaryType
      (LevelTree.lev a) hj (LevelTree.lev v) hf :=
    eq_of_heq (Sigma.mk.inj_iff.mp hRaw).2
  refine ⟨hf.trans u.level_le_size, ?_⟩
  rw [hRecord]
  exact ⟨fun i j t => u.same_socle.1
      ⟨i.val, lt_of_lt_of_le i.isLt hf⟩
      ⟨j.val, lt_of_lt_of_le j.isLt hf⟩ t,
    fun i t => u.same_socle.2.1
      ⟨i.val, lt_of_lt_of_le i.isLt hf⟩ t,
    fun i t => u.same_socle.2.2.1
      ⟨i.val, lt_of_lt_of_le i.isLt hf⟩ t,
    fun i j => u.same_socle.2.2.2
      ⟨i.val, lt_of_lt_of_le i.isLt hf⟩
      ⟨j.val, lt_of_lt_of_le j.isLt hf⟩⟩

/-- The complete type of an ordinary vertex is obtained from the base
tables, independently of which full type above that socle was chosen. -/
theorem ordinaryType_eq (u : TypeProfile A)
    (j : Nat) (hj : j < u.level) (f : Nat) (hf : f ≤ u.level) :
    u.1.1.2.ordinaryType j hj f hf = A.str.partialTypeAt f j := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x <;> cases y <;> exact u.same_socle.1 _ _ t
    · intro x t
      cases x <;> exact u.same_socle.2.1 _ t
    · intro x t
      cases x <;> exact u.same_socle.2.2.1 _ t
  · intro x y
    cases x <;> cases y <;> exact u.same_socle.2.2.2 _ _

/-- The list of actual parameter levels is determined by the base's free
cut, including the empty list at cut zero. -/
theorem canonical_parameter_levels (u : TypeProfile A)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) (hBelow : b ≤ u.1) :
    p.map (fun v => v.1.1) =
      if A.str.freeLevel a.1.1 = 0 then [] else [A.str.freeLevel a.1.1] := by
  obtain ⟨ell, f, hf, Q, hA, hB, _, hValid, hParam, _⟩ := hStep
  have hSocle : SameOrdinaryAtCut Q (A.str.partialTypeAt (ell + 1) 0) := by
    have hSocle := (u.mem_of_le hBelow).2
    have hTransport := congrArg
      (fun q : RawPartialTypeNode db du dd =>
        SameOrdinaryAtCut q.2 (A.str.partialTypeAt q.1 0)) hB
    exact hTransport.mp hSocle
  have hFree : A.str.freeLevel ell = f :=
    sameOrdinaryAtCut_freeLevel_eq_of_validNewColumn A.str Q hSocle f hf hValid
  have hLevel : a.1.1 = ell := congrArg Sigma.fst hA
  rw [hLevel, hFree]
  have hLevels := congrArg
    (List.map (fun v : RawPartialTypeNode db du dd => v.1)) hParam
  by_cases hZero : f = 0
  · simpa [List.map_map, PartialTypeWithE.canonicalParameterRecord, hZero] using hLevels
  · simpa [List.map_map, PartialTypeWithE.canonicalParameterRecord, hZero] using hLevels

/-- The actual partial type of a vertex belongs to the complete profile. -/
noncomputable abbrev vertexType (A : FiniteTypeBase family) (v : Fin A.size) : TypeProfile A :=
  ⟨⟨A.str.rawTypeAtFree v.val, ⟨A.str, v.val, v.isLt, A.avoids, rfl⟩⟩,
    ⟨(A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt),
      by exact ⟨by intros; rfl, by intros; rfl, by intros; rfl, by intros; rfl⟩⟩⟩

@[simp] theorem vertexType_level (A : FiniteTypeBase family) (v : Fin A.size) :
    (vertexType A v).level = A.str.freeLevel v.val := rfl

end TypeProfile

namespace CoherentTypeProfileMap

variable {A B : FiniteTypeBase family}

/-- The natural-number value of the coherent image of a source cut. -/
def levelMap (h : CoherentTypeProfileMap A B) (n : Nat) (hn : n ≤ A.size) : Nat :=
  (h.cutMap ⟨n, Nat.lt_succ_iff.mpr hn⟩).val

theorem levelMap_congr (h : CoherentTypeProfileMap A B)
    {i j : Nat} (hi : i ≤ A.size) (hj : j ≤ A.size) (hij : i = j) :
    h.levelMap i hi = h.levelMap j hj := by
  cases hij
  rfl

@[simp] theorem levelMap_level (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) : h.levelMap u.level u.level_le_size = (h u).1.1 :=
  (h.level_eq u).symm

theorem levelMap_strictMono (h : CoherentTypeProfileMap A B)
    {i j : Nat} (hi : i ≤ A.size) (hj : j ≤ A.size) (hij : i < j) :
    h.levelMap i hi < h.levelMap j hj :=
  h.cut_strictMono hij

theorem levelMap_mono (h : CoherentTypeProfileMap A B)
    {i j : Nat} (hi : i ≤ A.size) (hj : j ≤ A.size) (hij : i ≤ j) :
    h.levelMap i hi ≤ h.levelMap j hj :=
  h.cut_strictMono.monotone hij

@[simp] theorem levelMap_zero (h : CoherentTypeProfileMap A B) :
    h.levelMap 0 (Nat.zero_le A.size) = 0 :=
  congrArg Fin.val h.cut_zero

@[simp] theorem levelMap_top (h : CoherentTypeProfileMap A B) :
    h.levelMap A.size le_rfl = B.size :=
  congrArg Fin.val h.cut_top

/-- The increasing map of ordinary vertices determined by the cut map. -/
def vertexMap (h : CoherentTypeProfileMap A B) (v : Fin A.size) : Fin B.size :=
  ⟨h.levelMap v.val (Nat.le_of_lt v.isLt), by
    rw [← h.levelMap_top]
    exact h.levelMap_strictMono (Nat.le_of_lt v.isLt) le_rfl v.isLt⟩

theorem vertexMap_strictMono (h : CoherentTypeProfileMap A B) :
    StrictMono h.vertexMap := by
  intro i j hij
  exact h.levelMap_strictMono (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt) hij

theorem vertexMap_injective (h : CoherentTypeProfileMap A B) :
    Function.Injective h.vertexMap := h.vertexMap_strictMono.injective

@[simp] theorem levelMap_ancestor (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) (n : Nat) (hn : n ≤ u.level) :
    (h (u.ancestor n hn)).1.1 = h.levelMap n (hn.trans u.level_le_size) :=
  h.level_eq (u.ancestor n hn)

/-- The ordinary coordinates retained in the image of a full type. -/
def retainedIndex (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) (i : Fin u.level) : Fin (h u).1.1 :=
  ⟨h.levelMap i.val ((Nat.le_of_lt i.isLt).trans u.level_le_size), by
    rw [← h.levelMap_level u]
    exact h.levelMap_strictMono ((Nat.le_of_lt i.isLt).trans u.level_le_size)
      u.level_le_size i.isLt⟩

/-- Coherence identifies each prefix image with the unique prefix at its
prescribed image level, including all newly inserted coordinates. -/
theorem ancestor_transport (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) (n : Nat) (hn : n ≤ u.level) :
    h (u.ancestor n hn) =
      admissibleKptAncestor (h u) (h.levelMap n (hn.trans u.level_le_size))
        (by rw [← h.levelMap_level u]
            exact h.levelMap_mono (hn.trans u.level_le_size) u.level_le_size hn) := by
  have hPrefix := h.prefix (u.ancestor n hn) u (u.ancestor_le n hn)
  have hLevel := h.levelMap_ancestor u n hn
  have hBound : h.levelMap n (hn.trans u.level_le_size) ≤ (h u).1.1 := by
    rw [← h.levelMap_level u]
    exact h.levelMap_mono (hn.trans u.level_le_size) u.level_le_size hn
  exact (LevelTree.eq_ancestor_of_le hPrefix hLevel hBound).trans
    (admissibleKpt_levelTree_ancestor_eq (h u) _ hBound)

/-- Every decomposition below a profile node is a literal domain equation,
including its complete list of canonical parameters. -/
theorem preserves_decomposition (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) (n : Nat) (hn : n < u.level) :
    ∃ (p : List (TypeProfile A)) (c : AdmissibleKptSigma family)
      (d : AdmissibleKptNode family),
      let a := u.ancestor n (Nat.le_of_lt hn)
      let b := u.ancestor (n + 1) (Nat.succ_le_iff.mpr hn)
      (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c = some b.1 ∧
      (admissibleKptSTree family).succ (h a) (p.map h) c = some d ∧
      d ≤ h u := by
  let a := u.ancestor n (Nat.le_of_lt hn)
  let b := u.ancestor (n + 1) (Nat.succ_le_iff.mpr hn)
  have hau : a.1 ≤ u.1 := u.ancestor_le _ _
  have hbu : b.1 ≤ u.1 := u.ancestor_le _ _
  have hab : a.1 ≤ b.1 := by
    rcases LevelTree.comparable_below hau hbu with hab | hba
    · exact hab
    · have hlevel := LevelTree.level_le_of_le hba
      change n + 1 ≤ n at hlevel
      omega
  have hcover : a.1 ⋖ b.1 :=
    LevelTree.covBy_of_le_level_succ hab rfl
  obtain ⟨p, c, hSource⟩ := (admissibleKptSTree family).s3 hcover
  have hp : ∀ v, v ∈ p → v ∈ A.profile :=
    fun v hv => u.parameter_mem (canonicalKptSucc_spec family hSource) hbu v hv
  let q : List (TypeProfile A) := p.attach.map (fun v => ⟨v.val, hp v.val v.property⟩)
  have hq : q.map Subtype.val = p := by
    simpa only [q, List.map_map, Function.comp_def] using List.attach_map_subtype_val p
  have hSource' : (admissibleKptSTree family).succ a.1 (q.map Subtype.val) c =
      some b.1 := by rw [hq]; exact hSource
  obtain ⟨d, hMapped, hd⟩ := h.weak_succ a b q c hSource'
  exact ⟨q, c, d, hSource', hMapped, hd.trans (h.prefix b u hbu)⟩

/-- Fixed roots and prefixes preserve the complete distinguished singleton. -/
theorem preserves_type_singleton (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) :
    (h u).1.2.restrict (Nat.zero_le (h u).1.1) =
      u.1.1.2.restrict (Nat.zero_le u.level) := by
  let r := u.ancestor 0 (Nat.zero_le _)
  have hru : r.1 ≤ u.1 := u.ancestor_le _ _
  have hrhu : r.1 ≤ h u := by
    rw [← h.root_fixed r rfl]
    exact h.prefix r u hru
  exact (rawPrefix_preserves_type_singleton hrhu).trans
    (rawPrefix_preserves_type_singleton hru).symm

/-- The weak successor retains the full terminal letter at every source cut. -/
theorem preserves_type_pair (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) (i : Nat) (hi : i < u.level) :
    ∃ hI : h.levelMap i ((Nat.le_of_lt hi).trans u.level_le_size) < (h u).1.1,
      (h u).1.2.pairAt (h.levelMap i ((Nat.le_of_lt hi).trans u.level_le_size)) hI =
        u.1.1.2.pairAt i hi := by
  let a := u.ancestor i (Nat.le_of_lt hi)
  let b := u.ancestor (i + 1) (Nat.succ_le_iff.mpr hi)
  obtain ⟨p, c, d, hSource, hMapped, hBelow⟩ := h.preserves_decomposition u i hi
  have hSource' : (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c =
      some b.1 := hSource
  have hMapped' : (admissibleKptSTree family).succ (h a) (p.map h) c = some d :=
    hMapped
  obtain ⟨hOld, hOldPair⟩ := canonicalKptStep_letter_in_upper family
    (canonicalKptSucc_spec family hSource') (u.ancestor_le (i + 1) _)
  obtain ⟨hNew, hNewPair⟩ := canonicalKptStep_letter_in_upper family
    (canonicalKptSucc_spec family hMapped') hBelow
  have ha : LevelTree.lev a.1 = i := rfl
  have hImage : LevelTree.lev (h a) =
      h.levelMap i ((Nat.le_of_lt hi).trans u.level_le_size) := h.level_eq a
  have hPair : u.1.1.2.pairAt i hi = c.1 := by
    simpa only [ha] using hOldPair
  have hResult : ∃ hI : LevelTree.lev (h a) < (h u).1.1,
      (h u).1.2.pairAt (LevelTree.lev (h a)) hI = u.1.1.2.pairAt i hi :=
    ⟨hNew, hNewPair.trans hPair.symm⟩
  simpa only [hImage] using hResult

/-- Every nonempty canonical parameter is present as its complete image
record inside the image of the upper type. -/
theorem transports_parameter_record (h : CoherentTypeProfileMap A B)
    {a b u : TypeProfile A} {p : List (TypeProfile A)}
    {c : AdmissibleKptSigma family}
    (hSource : (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c = some b.1)
    (hBelow : b.1 ≤ u.1) (v : TypeProfile A) (hv : v ∈ p) :
    ∃ (hj : (h a).1.1 < (h u).1.1) (hf : (h v).1.1 ≤ (h u).1.1),
      (h v).1 = (⟨(h v).1.1,
        (h u).1.2.ordinaryType (h a).1.1 hj (h v).1.1 hf⟩ :
          RawPartialTypeNode db du dd) := by
  obtain ⟨d, hMapped, hd⟩ := h.weak_succ a b p c hSource
  exact canonicalKptStep_parameter_in_upper family
    (canonicalKptSucc_spec family hMapped) (hd.trans (h.prefix b u hBelow))
    (h v) (List.mem_map.mpr ⟨v, hv, rfl⟩)

/-- The empty-or-singleton canonical parameter convention forces exact
transport of the ordinary vertex's free cut, including cut zero. -/
theorem transports_freeLevel_at_step (h : CoherentTypeProfileMap A B)
    {a b u : TypeProfile A} {p : List (TypeProfile A)}
    {c : AdmissibleKptSigma family}
    (hSource : (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c = some b.1)
    (hBelow : b.1 ≤ u.1) :
    B.str.freeLevel (h a).1.1 =
      h.levelMap (A.str.freeLevel a.level)
        ((A.str.freeLevel_le a.level).trans a.level_le_size) := by
  obtain ⟨d, hMapped, hd⟩ := h.weak_succ a b p c hSource
  have hSourceLevels : p.map (fun v => v.level) =
      if A.str.freeLevel a.level = 0 then [] else [A.str.freeLevel a.level] := by
    simpa only [List.map_map, Function.comp_def] using
      u.canonical_parameter_levels (canonicalKptSucc_spec family hSource) hBelow
  have hTargetLevels : p.map (fun v => (h v).1.1) =
      if B.str.freeLevel (h a).1.1 = 0 then [] else [B.str.freeLevel (h a).1.1] := by
    simpa only [List.map_map, Function.comp_def] using
      (h.mapNode u).canonical_parameter_levels (canonicalKptSucc_spec family hMapped)
        (hd.trans (h.prefix b u hBelow))
  cases p with
  | nil =>
      have hAZero : A.str.freeLevel a.level = 0 := by
        by_contra hNot
        simp [hNot] at hSourceLevels
      have hBZero : B.str.freeLevel (h a).1.1 = 0 := by
        by_contra hNot
        simp [hNot] at hTargetLevels
      exact hBZero.trans (h.levelMap_zero.symm.trans
        (h.levelMap_congr
          ((A.str.freeLevel_le a.level).trans a.level_le_size)
          (Nat.zero_le A.size) hAZero).symm)
  | cons v p =>
      have hAHead : v.level = A.str.freeLevel a.level := by
        by_cases hZero : A.str.freeLevel a.level = 0
        · simp [hZero] at hSourceLevels
        · have hh : v.level :: p.map (fun w => w.level) = [A.str.freeLevel a.level] := by
            simpa only [List.map_cons, if_neg hZero] using hSourceLevels
          exact (List.cons.inj hh).1
      have hBHead : (h v).1.1 = B.str.freeLevel (h a).1.1 := by
        by_cases hZero : B.str.freeLevel (h a).1.1 = 0
        · simp [hZero] at hTargetLevels
        · have hh : (h v).1.1 :: p.map (fun w => (h w).1.1) =
              [B.str.freeLevel (h a).1.1] := by
            simpa only [List.map_cons, if_neg hZero] using hTargetLevels
          exact (List.cons.inj hh).1
      exact hBHead.symm.trans ((h.levelMap_level v).symm.trans
        (h.levelMap_congr v.level_le_size
          ((A.str.freeLevel_le a.level).trans a.level_le_size) hAHead))

/-- Exact free-level transport for the underlying finite vertex map. -/
theorem vertexMap_freeLevel (h : CoherentTypeProfileMap A B) (v : Fin A.size) :
    B.str.freeLevel (h.vertexMap v).val =
      h.levelMap (A.str.freeLevel v.val)
        ((A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt)) := by
  let u := TypeProfile.cap A
  obtain ⟨p, c, d, hSource, _hMapped, _hBelow⟩ :=
    h.preserves_decomposition u v.val v.isLt
  have hFree := h.transports_freeLevel_at_step hSource
    (u.ancestor_le (v.val + 1) (Nat.succ_le_iff.mpr v.isLt))
  simpa only [levelMap_ancestor, TypeProfile.ancestor_level, vertexMap] using hFree

/-- Inside a canonical parameter's free socle, ordinary pairs are precisely
the already recovered type pairs of that parameter. -/
theorem preserves_ordinary_pair_in_parameter (h : CoherentTypeProfileMap A B)
    {a b u : TypeProfile A} {p : List (TypeProfile A)}
    {c : AdmissibleKptSigma family}
    (hSource : (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c = some b.1)
    (hBelow : b.1 ≤ u.1) (v : TypeProfile A) (hv : v ∈ p)
    (i : Nat) (hi : i < v.level) :
    ∃ (hOldI : i < u.level) (hOldJ : a.level < u.level)
      (hNewI : h.levelMap i ((Nat.le_of_lt hi).trans v.level_le_size) < (h u).1.1)
      (hNewJ : (h a).1.1 < (h u).1.1),
      (h u).1.2.ordinaryPair
          ⟨h.levelMap i ((Nat.le_of_lt hi).trans v.level_le_size), hNewI⟩
          ⟨(h a).1.1, hNewJ⟩ =
        u.1.1.2.ordinaryPair ⟨i, hOldI⟩ ⟨a.level, hOldJ⟩ := by
  obtain ⟨hOldJ, hOldF, hOldRaw⟩ := canonicalKptStep_parameter_in_upper family
    (canonicalKptSucc_spec family hSource) hBelow v.1
    (List.mem_map.mpr ⟨v, hv, rfl⟩)
  obtain ⟨hNewJ, hNewF, hNewRaw⟩ := h.transports_parameter_record hSource hBelow v hv
  have hOldRecord : v.1.1.2 = u.1.1.2.ordinaryType
      a.level hOldJ v.level hOldF :=
    eq_of_heq (Sigma.mk.inj_iff.mp hOldRaw).2
  have hNewRecord : (h v).1.2 = (h u).1.2.ordinaryType
      (h a).1.1 hNewJ (h v).1.1 hNewF :=
    eq_of_heq (Sigma.mk.inj_iff.mp hNewRaw).2
  obtain ⟨hIn, hPair⟩ := h.preserves_type_pair v i hi
  refine ⟨lt_of_lt_of_le hi hOldF, hOldJ,
    lt_of_lt_of_le hIn hNewF, hNewJ, ?_⟩
  have hNew := PartialTypeWithE.ordinaryType_pairAt (h u).1.2
    (h a).1.1 hNewJ (h v).1.1 hNewF
    (h.levelMap i ((Nat.le_of_lt hi).trans v.level_le_size)) hIn
  have hOld := PartialTypeWithE.ordinaryType_pairAt u.1.1.2
    a.level hOldJ v.level hOldF i hi
  rw [hNewRecord, hOldRecord] at hPair
  exact hNew.symm.trans (hPair.trans hOld)

/-- Outside every parameter socle the canonical no-new-tuples clause gives
empty crossings on both sides. Thus all ordinary pairs are recovered. -/
theorem preserves_ordinary_pair (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) (i j : Nat) (hij : i < j) (hj : j < u.level) :
    ∃ (hI : h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size) < (h u).1.1)
      (hJ : h.levelMap j ((Nat.le_of_lt hj).trans u.level_le_size) < (h u).1.1),
      (h u).1.2.ordinaryPair
          ⟨h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size), hI⟩
          ⟨h.levelMap j ((Nat.le_of_lt hj).trans u.level_le_size), hJ⟩ =
        u.1.1.2.ordinaryPair ⟨i, hij.trans hj⟩ ⟨j, hj⟩ := by
  let a := u.ancestor j (Nat.le_of_lt hj)
  let b := u.ancestor (j + 1) (Nat.succ_le_iff.mpr hj)
  have ha : a.level = j := rfl
  have hb : b.1 ≤ u.1 := u.ancestor_le _ _
  have hFa : (h a).1.1 = h.levelMap j ((Nat.le_of_lt hj).trans u.level_le_size) :=
    h.level_eq a
  obtain ⟨p, c, d, hSource, hMapped, hBelow⟩ := h.preserves_decomposition u j hj
  have hSource' : (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c =
      some b.1 := hSource
  by_cases hInside : ∃ v, v ∈ p ∧ i < v.level
  · obtain ⟨v, hv, hi⟩ := hInside
    obtain ⟨hOldI, hOldJ, hNewI, hNewJ, hPair⟩ :=
      h.preserves_ordinary_pair_in_parameter hSource' hb v hv i hi
    have hPair' : ∃
        (hI : h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size) < (h u).1.1)
        (hJ : (h a).1.1 < (h u).1.1),
        (h u).1.2.ordinaryPair
            ⟨h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size), hI⟩
            ⟨(h a).1.1, hJ⟩ =
          u.1.1.2.ordinaryPair ⟨i, hOldI⟩ ⟨a.level, hOldJ⟩ :=
      ⟨hNewI, hNewJ, hPair⟩
    simpa only [ha, hFa] using hPair'
  · have hBeyond : ∀ v, v ∈ p → v.level ≤ i := by
      intro v hv
      by_contra hNot
      exact hInside ⟨v, hv, by omega⟩
    have hOldBeyond : ∀ v, v ∈ p.map Subtype.val → LevelTree.lev v ≤ i := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      exact hBeyond w hw
    obtain ⟨hOldI, hOldJ, hOldEmpty⟩ :=
      canonicalKptStep_empty_cross_after_parameters family
        (canonicalKptSucc_spec family hSource') hb i hij hOldBeyond
    have hNewBeyond : ∀ v, v ∈ p.map h →
        LevelTree.lev v ≤
          h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size) := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      change (h w).1.1 ≤ _
      rw [← h.levelMap_level w]
      exact h.levelMap_mono w.level_le_size
        ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size) (hBeyond w hw)
    have hNewLess :
        h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size) <
          LevelTree.lev (h a) := by
      change _ < (h a).1.1
      rw [hFa]
      exact h.levelMap_strictMono
        ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size)
        ((Nat.le_of_lt hj).trans u.level_le_size) hij
    have hMapped' : (admissibleKptSTree family).succ (h a) (p.map h) c = some d :=
      hMapped
    obtain ⟨hNewI, hNewJ, hNewEmpty⟩ :=
      canonicalKptStep_empty_cross_after_parameters family
        (canonicalKptSucc_spec family hMapped') hBelow
        (h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size))
        hNewLess hNewBeyond
    obtain ⟨hI, hIPair⟩ := h.preserves_type_pair u i (hij.trans hj)
    obtain ⟨hJ, hJPair⟩ := h.preserves_type_pair u j hj
    refine ⟨hI, hJ, ?_⟩
    apply ordinaryPair_eq_of_empty_cross u.1.1.2 (h u).1.2
      ⟨i, hij.trans hj⟩ ⟨j, hj⟩
      ⟨h.levelMap i ((Nat.le_of_lt (hij.trans hj)).trans u.level_le_size), hI⟩
      ⟨h.levelMap j ((Nat.le_of_lt hj).trans u.level_le_size), hJ⟩
      hIPair hJPair
    · exact hOldEmpty
    · have hFa' : LevelTree.lev (h a) =
          h.levelMap j ((Nat.le_of_lt hj).trans u.level_le_size) := hFa
      simpa only [hFa'] using hNewEmpty

/-- The entire retained record, including all negative L facts and auxiliary
E facts, is forced by the finite coherent successor laws alone. -/
theorem recovers_complete_record (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) :
    (h u).1.2.reindexOrdinary (h.retainedIndex u) = u.1.1.2 := by
  let index := h.retainedIndex u
  have hSingleton := h.preserves_type_singleton u
  have hPair (i : Fin u.level) :
      (h u).1.2.pairAt (index i).val (index i).isLt =
        u.1.1.2.pairAt i.val i.isLt := by
    obtain ⟨hI, hPair⟩ := h.preserves_type_pair u i.val i.isLt
    exact hPair
  have hOrdinary (i j : Fin u.level) :
      (∀ t : Fin db,
        (h u).1.2.lReduct.binary (some (index i)) (some (index j)) t =
          u.1.1.2.lReduct.binary (some i) (some j) t) ∧
      (h u).1.2.eRelation (some (index i)) (some (index j)) =
        u.1.1.2.eRelation (some i) (some j) := by
    rcases lt_trichotomy i.val j.val with hLess | hEqual | hGreater
    · obtain ⟨hi, hj, hPair⟩ := h.preserves_ordinary_pair u i.val j.val hLess j.isLt
      exact ⟨fun t => congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) none t) hPair,
        congrArg (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) none) hPair⟩
    · have hij : i = j := Fin.ext hEqual
      subst j
      exact ⟨fun t => congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) (some 0) t) (hPair i),
        congrArg (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) (some 0)) (hPair i)⟩
    · obtain ⟨hj, hi, hPair⟩ := h.preserves_ordinary_pair u j.val i.val hGreater i.isLt
      exact ⟨fun t => congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary none (some 0) t) hPair,
        congrArg (fun P : PartialTypeWithE 1 db du dd => P.eRelation none (some 0)) hPair⟩
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x <;> cases y
      · exact congrArg
          (fun P : PartialTypeWithE 0 db du dd => P.lReduct.binary none none t) hSingleton
      · exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary none (some 0) t) (hPair _)
      · exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) none t) (hPair _)
      · exact (hOrdinary _ _).1 t
    · intro x t
      cases x
      · exact congrArg
          (fun P : PartialTypeWithE 0 db du dd => P.lReduct.unary none t) hSingleton
      · exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.unary (some 0) t) (hPair _)
    · intro x t
      cases x
      · exact congrArg
          (fun P : PartialTypeWithE 0 db du dd => P.lReduct.diagonal none t) hSingleton
      · exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.diagonal (some 0) t) (hPair _)
  · intro x y
    cases x <;> cases y
    · exact congrArg
        (fun P : PartialTypeWithE 0 db du dd => P.eRelation none none) hSingleton
    · exact congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.eRelation none (some 0)) (hPair _)
    · exact congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) none) (hPair _)
    · exact (hOrdinary _ _).2

/-- Every retained ordinary table agrees with the source base. -/
theorem recovers_ordinary_socle (h : CoherentTypeProfileMap A B)
    (u : TypeProfile A) :
    SameOrdinaryAtCut
      ((B.str.partialTypeAt (h u).1.1 0).reindexOrdinary (h.retainedIndex u))
      (A.str.partialTypeAt u.level 0) := by
  have hRecord := h.recovers_complete_record u
  have hSocle := h.maps_socle u
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j t
    exact (hSocle.1 (h.retainedIndex u i) (h.retainedIndex u j) t).symm.trans
      ((congrArg (fun P : PartialTypeWithE u.level db du dd =>
        P.lReduct.binary (some i) (some j) t) hRecord).trans
          (u.same_socle.1 i j t))
  · intro i t
    exact (hSocle.2.1 (h.retainedIndex u i) t).symm.trans
      ((congrArg (fun P : PartialTypeWithE u.level db du dd =>
        P.lReduct.unary (some i) t) hRecord).trans (u.same_socle.2.1 i t))
  · intro i t
    exact (hSocle.2.2.1 (h.retainedIndex u i) t).symm.trans
      ((congrArg (fun P : PartialTypeWithE u.level db du dd =>
        P.lReduct.diagonal (some i) t) hRecord).trans (u.same_socle.2.2.1 i t))
  · intro i j
    exact (hSocle.2.2.2 (h.retainedIndex u i) (h.retainedIndex u j)).symm.trans
      ((congrArg (fun P : PartialTypeWithE u.level db du dd =>
        P.eRelation (some i) (some j)) hRecord).trans (u.same_socle.2.2.2 i j))

/-- The ordinary vertex map is an induced ordered L+ embedding. -/
theorem vertexMap_preserves_atoms (h : CoherentTypeProfileMap A B) :
    (∀ i j : Fin A.size, ∀ t : Fin db,
      B.str.L.binary (h.vertexMap i).val (h.vertexMap j).val t =
        A.str.L.binary i.val j.val t) ∧
    (∀ i : Fin A.size, ∀ t : Fin du,
      B.str.L.unary (h.vertexMap i).val t = A.str.L.unary i.val t) ∧
    (∀ i : Fin A.size, ∀ t : Fin dd,
      B.str.L.diagonal (h.vertexMap i).val t = A.str.L.diagonal i.val t) ∧
    (∀ i j : Fin A.size,
      B.str.E (h.vertexMap i).val (h.vertexMap j).val = A.str.E i.val j.val) :=
  h.recovers_ordinary_socle (TypeProfile.cap A)

/-- The image of each actual partial type is exactly the partial type of
the image vertex, with its full target socle and its true free cut. -/
theorem vertexType_transport (h : CoherentTypeProfileMap A B) (v : Fin A.size) :
    h (TypeProfile.vertexType A v) =
      (TypeProfile.vertexType B (h.vertexMap v)).1 := by
  by_cases hZero : A.str.freeLevel v.val = 0
  · have hBZero : B.str.freeLevel (h.vertexMap v).val = 0 := by
      exact (h.vertexMap_freeLevel v).trans
        ((h.levelMap_congr
          ((A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt))
          (Nat.zero_le A.size) hZero).trans h.levelMap_zero)
    have hAtoms := h.vertexMap_preserves_atoms
    have hRecord : B.str.partialTypeAt 0 (h.vertexMap v).val =
        A.str.partialTypeAt 0 v.val := by
      apply PartialTypeWithE.eq_of_atoms
      · apply RelationalPrefixType.eq_of_atoms
        · intro x y t
          cases x with
          | some i => exact i.elim0
          | none =>
              cases y with
              | some j => exact j.elim0
              | none => exact hAtoms.1 v v t
        · intro x t
          cases x with
          | some i => exact i.elim0
          | none => exact hAtoms.2.1 v t
        · intro x t
          cases x with
          | some i => exact i.elim0
          | none => exact hAtoms.2.2.1 v t
      · intro x y
        cases x with
        | some i => exact i.elim0
        | none =>
            cases y with
            | some j => exact j.elim0
            | none => exact hAtoms.2.2.2 v v
    rw [h.root_fixed (TypeProfile.vertexType A v) hZero]
    apply Subtype.ext
    change (⟨A.str.freeLevel v.val,
        A.str.partialTypeAt (A.str.freeLevel v.val) v.val⟩ : RawPartialTypeNode db du dd) =
      ⟨B.str.freeLevel (h.vertexMap v).val,
        B.str.partialTypeAt (B.str.freeLevel (h.vertexMap v).val) (h.vertexMap v).val⟩
    rw [hZero, hBZero]
    exact congrArg (Sigma.mk 0) hRecord.symm
  · let u := TypeProfile.cap A
    let a := u.ancestor v.val (Nat.le_of_lt v.isLt)
    let b := u.ancestor (v.val + 1) (Nat.succ_le_iff.mpr v.isLt)
    have hbu : b.1 ≤ u.1 := u.ancestor_le _ _
    obtain ⟨p, c, d, hSource, _hMapped, _hBelow⟩ :=
      h.preserves_decomposition u v.val v.isLt
    have hSource' : (admissibleKptSTree family).succ a.1 (p.map Subtype.val) c =
        some b.1 := hSource
    have hLevels : p.map (fun w => w.level) = [A.str.freeLevel v.val] := by
      have hLevels :=
        u.canonical_parameter_levels (canonicalKptSucc_spec family hSource') hbu
      simp only [List.map_map, Function.comp_def] at hLevels
      change p.map (fun w => w.level) =
        if A.str.freeLevel v.val = 0 then [] else [A.str.freeLevel v.val] at hLevels
      simpa only [if_neg hZero] using hLevels
    have hMem : A.str.freeLevel v.val ∈ p.map (fun w => w.level) := by
      rw [hLevels]
      simp
    obtain ⟨w, hw, hWLevel⟩ := List.mem_map.mp hMem
    change w.level = A.str.freeLevel v.val at hWLevel
    obtain ⟨hOldJ, hOldF, hOldRaw⟩ := canonicalKptStep_parameter_in_upper family
      (canonicalKptSucc_spec family hSource') hbu w.1
      (List.mem_map.mpr ⟨w, hw, rfl⟩)
    change a.level < u.level at hOldJ
    change w.level ≤ u.level at hOldF
    change w.1.1 = (⟨w.level,
      u.1.1.2.ordinaryType a.level hOldJ w.level hOldF⟩ :
        RawPartialTypeNode db du dd) at hOldRaw
    rw [u.ordinaryType_eq a.level hOldJ w.level hOldF] at hOldRaw
    have hWRaw : w.1.1 = A.str.rawTypeAtFree v.val := by
      change w.1.1 = (⟨w.level, A.str.partialTypeAt w.level v.val⟩ :
        RawPartialTypeNode db du dd) at hOldRaw
      calc
        w.1.1 = (⟨w.level, A.str.partialTypeAt w.level v.val⟩ :
          RawPartialTypeNode db du dd) := hOldRaw
        _ = A.str.rawTypeAtFree v.val := by rw [hWLevel]; rfl
    have hW : w = TypeProfile.vertexType A v := Subtype.ext (Subtype.ext hWRaw)
    obtain ⟨hNewJ, hNewF, hNewRaw⟩ := h.transports_parameter_record hSource' hbu w hw
    have hNewOrd := (h.mapNode u).ordinaryType_eq (h a).1.1 hNewJ (h w).1.1 hNewF
    change (h u).1.2.ordinaryType (h a).1.1 hNewJ (h w).1.1 hNewF =
      B.str.partialTypeAt (h w).1.1 (h a).1.1 at hNewOrd
    rw [hNewOrd] at hNewRaw
    have hNewLevel : (h w).1.1 = B.str.freeLevel (h.vertexMap v).val := by
      exact (h.levelMap_level w).symm.trans
        ((h.levelMap_congr w.level_le_size
          ((A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt)) hWLevel).trans
            (h.vertexMap_freeLevel v).symm)
    have hVertexLevel : (h a).1.1 = (h.vertexMap v).val :=
      h.level_eq a
    apply Subtype.ext
    calc
      (h (TypeProfile.vertexType A v)).1 = (h w).1 := by rw [hW]
      _ = (⟨(h w).1.1,
          B.str.partialTypeAt (h w).1.1 (h a).1.1⟩ : RawPartialTypeNode db du dd) :=
        hNewRaw
      _ = B.str.rawTypeAtFree (h.vertexMap v).val := by
        rw [hNewLevel, hVertexLevel]
        rfl

end CoherentTypeProfileMap

end SuccessorTree.V10
