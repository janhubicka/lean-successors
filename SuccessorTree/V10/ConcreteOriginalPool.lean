import SuccessorTree.V10.AdmissibleSigmaSTree
import SuccessorTree.V10.OriginalPoolEnvelope

/-!
# The original-pool invariant for the actual admissible Kpt successor

The generic pool lemmas assumed a canonical parameter rule. Here the rule
is proved for the constructed admissible Kpt S-tree and a single genuine
forbidden-free ambient partial structure A. The successor graph determines
the free cut from its complete E column; extraction then identifies its
only possible parameter with the actual type of the crossed vertex of A.

Thus the actual Section 5 closure stays represented by a pool containing
the initial originals and all selected vertices with positive free level.
There is no hypothesis asserting parameter closure or a trace dictionary.
All originals retain their addresses in A, including when their types agree.
-/

namespace SuccessorTree.V10

/-- The actual admissible type of a carrier vertex in one fixed ambient. -/
noncomputable def EnumeratedPartialStructure.kptOriginal
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size) : AdmissibleKptNode family :=
  ⟨A.rawTypeAtFree v.val, ⟨A, v.val, v.isLt, hAvoid, rfl⟩⟩

/-- Every represented prefix is its literal complete induced L+ record. -/
theorem kpt_prefix_raw_eq_ambient
    {db du dd : Nat} (A : EnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size) (a : AdmissibleKptNode family)
    (ha : a ≤ A.kptOriginal family hAvoid v) :
    a.val = (⟨LevelTree.lev a, A.partialTypeAt (LevelTree.lev a) v.val⟩ :
      RawPartialTypeNode db du dd) := by
  have hraw : a.val ≤ A.rawTypeAtFree v.val := ha
  obtain ⟨hcut, hEq⟩ := hraw
  have hRecord : a.val.2 = A.partialTypeAt a.val.1 v.val := by
    change a.val.2 =
      (A.partialTypeAt (A.freeLevel v.val) v.val).restrict hcut at hEq
    exact hEq.trans (A.partialTypeAt_restrict a.val.1 (A.freeLevel v.val) v.val hcut)
  change (⟨a.val.1, a.val.2⟩ : RawPartialTypeNode db du dd) =
    ⟨a.val.1, A.partialTypeAt a.val.1 v.val⟩
  rw [hRecord]

/-- A successor whose output is extracted from A has precisely A's
empty-or-singleton parameter, including all unary, diagonal and E facts. -/
theorem canonicalKptStep_ambient_parameter
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size) (hCut : ell + 1 ≤ A.freeLevel v)
    {a b : AdmissibleKptNode family} {p : List (AdmissibleKptNode family)}
    {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b)
    (hb : b.val = (⟨ell + 1, A.partialTypeAt (ell + 1) v⟩ :
      RawPartialTypeNode db du dd)) :
    p.map Subtype.val =
      if A.freeLevel ell = 0 then [] else [A.rawTypeAtFree ell] := by
  obtain ⟨ell', f, hf, Q, _hBase, hTarget, _hLetter, hValid, hParam, _hGate⟩ := hStep
  have hRaw := hTarget.symm.trans hb
  have hLevel : ell' = ell := by
    have h := congrArg Sigma.fst hRaw
    change ell' + 1 = ell + 1 at h
    omega
  subst ell'
  have hQ : Q = A.partialTypeAt (ell + 1) v := by
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hRaw
  subst Q
  have hFree : f = A.freeLevel ell :=
    validNewColumn_freeCut_unique (A.partialTypeAt (ell + 1) v)
      f (A.freeLevel ell) hf (A.freeLevel_le ell) hValid
      (validNewColumn_of_extracted_partialType A v ell hv hCut)
  subst f
  have hRecord :
      (⟨A.freeLevel ell,
        (A.partialTypeAt (ell + 1) v).lastOrdinaryParameter (A.freeLevel ell) hf⟩ :
          RawPartialTypeNode db du dd) = A.rawTypeAtFree ell := by
    rw [partialTypeAt_lastOrdinaryParameter]
    rfl
  by_cases hz : A.freeLevel ell = 0
  · simpa [PartialTypeWithE.canonicalParameterRecord, hz] using hParam
  · simpa [PartialTypeWithE.canonicalParameterRecord, hz, hRecord] using hParam

/-- The canonical parameter rule along ANY represented prefix, for the
actual Option-valued successor and its admissible Sigma alphabet. -/
theorem admissibleKpt_crossing_parameter
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (v : Fin A.size) (a : AdmissibleKptNode family)
    (ha : a ≤ A.kptOriginal family hAvoid v)
    (i : Nat) (hi : i < LevelTree.lev a)
    (p : List (AdmissibleKptNode family)) (c : AdmissibleKptSigma family)
    (hStep : (admissibleKptSTree family).succ
      (LevelTree.ancestor a i (Nat.le_of_lt hi)) p c =
      some (LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hi))) :
    i < A.size ∧ p.map Subtype.val =
      if A.freeLevel i = 0 then [] else [A.rawTypeAtFree i] := by
  let b := LevelTree.ancestor a (i + 1) (Nat.succ_le_iff.mpr hi)
  have hb : b ≤ A.kptOriginal family hAvoid v :=
    (LevelTree.ancestor_le a (i + 1) (Nat.succ_le_iff.mpr hi)).trans ha
  have hbLevel : LevelTree.lev b = i + 1 := LevelTree.level_ancestor _ _ _
  have hCut : i + 1 ≤ A.freeLevel v.val := by
    have h := LevelTree.level_le_of_le hb
    rw [hbLevel] at h
    exact h
  have hiSize : i < A.size := by
    have hf := A.freeLevel_le v.val
    have hv := v.isLt
    omega
  have hbRaw := kpt_prefix_raw_eq_ambient A family hAvoid v b hb
  rw [hbLevel] at hbRaw
  rw [admissibleKptSTree_succ_eq] at hStep
  exact ⟨hiSize, canonicalKptStep_ambient_parameter family A v.val i v.isLt hCut
    (canonicalKptSucc_spec family hStep) hbRaw⟩

/-- Prefixes of the original types at the specified ambient addresses. -/
def ambientPrefixPool
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (V : Set (Fin A.size)) : Set (AdmissibleKptNode family) :=
  prefixesOf ((A.kptOriginal family hAvoid) '' V)

theorem ambientPrefixPool_mono
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    {U V : Set (Fin A.size)} (hUV : U ⊆ V) :
    ambientPrefixPool family A hAvoid U ⊆ ambientPrefixPool family A hAvoid V := by
  rintro a ⟨o, ⟨v, hv, rfl⟩, ha⟩
  exact ⟨A.kptOriginal family hAvoid v, ⟨v, hUV hv, rfl⟩, ha⟩

/-- Selected positive-free-level vertices suffice to close the actual
represented pool under every successor parameter. No abstract rule remains. -/
theorem ambientPrefixPool_parameterClosed
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat) (V : Set (Fin A.size))
    (hSelected : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.ParameterClosedOver (admissibleKptSTree family)
      (ambientPrefixPool family A hAvoid V) I := by
  intro a ha i hi hia p c hStep x hx
  obtain ⟨o, ⟨v, hv, rfl⟩, hao⟩ := ha
  obtain ⟨hiSize, hParam⟩ :=
    admissibleKpt_crossing_parameter family A hAvoid v a hao i hia p c hStep
  have hMem : x.val ∈ p.map Subtype.val := List.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hParam] at hMem
  by_cases hz : A.freeLevel i = 0
  · simp [hz] at hMem
  · have hPos : 0 < A.freeLevel i := by omega
    have hRaw : x.val = A.rawTypeAtFree i := by simpa [hz] using hMem
    let vi : Fin A.size := ⟨i, hiSize⟩
    have hxOriginal : x = A.kptOriginal family hAvoid vi := Subtype.ext hRaw
    exact ⟨A.kptOriginal family hAvoid vi,
      ⟨vi, hSelected vi hi hPos, rfl⟩, le_of_eq hxOriginal⟩

/-- Closure minimality now proves the invariant for the genuine Section 5
closure, using the concrete Kpt successor rather than an assumed interface. -/
theorem admissibleKpt_closure_subset_ambientPool
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (I : Set Nat) (V : Set (Fin A.size)) (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family A hAvoid V)
    (hSelected : ∀ i : Fin A.size, i.val ∈ I → 0 < A.freeLevel i.val → i ∈ V) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      ambientPrefixPool family A hAvoid V := by
  exact closure_subset_original_pool (admissibleKptSTree family) I X
    ((A.kptOriginal family hAvoid) '' V) hX
    (ambientPrefixPool_parameterClosed family A hAvoid I V hSelected)

/-- The stage pool retains the seed addresses and precisely those selected
addresses whose canonical parameter is nonempty. -/
def ambientStagePool {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) (U : Set (Fin A.size))
    (I : Set Nat) : Set (Fin A.size) :=
  U ∪ {i | i.val ∈ I ∧ 0 < A.freeLevel i.val}

/-- The stage invariant, with parameter closure discharged by construction
of the maintained pool. It holds for arbitrary I, hence at every stage. -/
theorem admissibleKpt_stage_closure_subset_pool
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (U : Set (Fin A.size)) (I : Set Nat) (X : Set (AdmissibleKptNode family))
    (hX : X ⊆ ambientPrefixPool family A hAvoid U) :
    SMTree.Envelope.closure (admissibleKptSTree family) I X ⊆
      ambientPrefixPool family A hAvoid (ambientStagePool A U I) := by
  apply admissibleKpt_closure_subset_ambientPool family A hAvoid I
    (ambientStagePool A U I) X
  · exact hX.trans (ambientPrefixPool_mono family A hAvoid (by
      intro v hv
      exact Or.inl hv))
  · intro i hi hPos
    exact Or.inr ⟨hi, hPos⟩

end SuccessorTree.V10
