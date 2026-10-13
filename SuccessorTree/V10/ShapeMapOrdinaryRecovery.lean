import SuccessorTree.V10.ShapeMapOrdinaryPairs
import Mathlib.Tactic

/-!
# Recovery of every retained ordinary L+ pair

Inside a canonical parameter's free socle, use full parameter-pair
transport. Outside all parameter socles, the genuine canonical
no-new-tuples clause makes both directed binary relations and both E
relations absent, before and after applying the shape map. The
singleton records are recovered from the retained terminal letters.

This completes ordinary-pair recovery for arbitrary genuine ShapeMaps;
no M2 or finite-age assumption is used, and image successors need only
lie below the actual image nodes.
-/

namespace SuccessorTree.V10

/-- Both directed L-crossings and E-crossings of a two-vertex record
are absent. Singleton data are deliberately unrestricted. -/
def EmptyPairCross {db du dd : Nat} (P : PartialTypeWithE 1 db du dd) : Prop :=
  (∀ t : Fin db, P.lReduct.binary (some 0) none t = false ∧
    P.lReduct.binary none (some 0) t = false) ∧
  P.eRelation (some 0) none = false ∧ P.eRelation none (some 0) = false

/-- Above every actual parameter level, the newly introduced ordinary
vertex has no L- or E-link to that coordinate. The empty parameter
case is included, not treated as an additional successor axiom. -/
theorem canonicalKptStep_empty_cross_after_parameters
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b u : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) (hBelow : b ≤ u)
    (i : Nat) (hi : i < LevelTree.lev a)
    (hBeyond : ∀ v, v ∈ p → LevelTree.lev v ≤ i) :
    ∃ (hI : i < LevelTree.lev u) (hJ : LevelTree.lev a < LevelTree.lev u),
      EmptyPairCross (u.1.2.ordinaryPair ⟨i, hI⟩ ⟨LevelTree.lev a, hJ⟩) := by
  obtain ⟨ell, f, hf, Q, hA, hB, _hC, hValid, hParam, _hGate⟩ := hStep
  have hALevel : LevelTree.lev a = ell := congrArg Sigma.fst hA
  have hCut : f ≤ i := by
    by_cases hz : f = 0
    · omega
    · have hMem : (⟨f, Q.lastOrdinaryParameter f hf⟩ : RawPartialTypeNode db du dd)
          ∈ p.map (fun v => v.1) := by
        rw [hParam]
        simp [PartialTypeWithE.canonicalParameterRecord, hz]
      obtain ⟨v, hv, hV⟩ := List.mem_map.mp hMem
      have hVLevel : LevelTree.lev v = f := congrArg Sigma.fst hV
      have hvi := hBeyond v hv
      omega
  have hPrefix : (⟨ell+1, Q⟩ : RawPartialTypeNode db du dd) ≤ u.1 := by
    rw [←hB]
    exact hBelow
  obtain ⟨hLe, hQ⟩ := hPrefix
  have hiEll : i < ell := by omega
  rw [hALevel]
  refine ⟨by change i < u.1.1; change ell+1 ≤ u.1.1 at hLe; omega,
    by change ell < u.1.1; change ell+1 ≤ u.1.1 at hLe; omega, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have h := hValid.noNewBinaryBeyondCut ⟨i, hiEll⟩ hCut t
    rw [hQ] at h
    exact h
  · have h := hValid.oldToNewE ⟨i, hiEll⟩
    rw [hQ] at h
    have hNot : ¬ i < f := by omega
    simpa only [hNot, decide_false] using h
  · have h := hValid.newToOldE ⟨i, hiEll⟩
    rw [hQ] at h
    exact h

/-- Empty crossings and equal retained singleton records determine
all atoms of an ordinary pair, including binary and E diagonals. -/
theorem ordinaryPair_eq_of_empty_cross
    {n m db du dd : Nat}
    (Q : PartialTypeWithE n db du dd) (R : PartialTypeWithE m db du dd)
    (i j : Fin n) (i' j' : Fin m)
    (hI : R.pairAt i'.val i'.isLt = Q.pairAt i.val i.isLt)
    (hJ : R.pairAt j'.val j'.isLt = Q.pairAt j.val j.isLt)
    (hOld : EmptyPairCross (Q.ordinaryPair i j))
    (hNew : EmptyPairCross (R.ordinaryPair i' j')) :
    R.ordinaryPair i' j' = Q.ordinaryPair i j := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x with
      | none =>
        cases y with
        | none => exact congrArg
            (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) (some 0) t) hJ
        | some k => exact (hNew.1 t).2.trans (hOld.1 t).2.symm
      | some k =>
        cases y with
        | none => exact (hNew.1 t).1.trans (hOld.1 t).1.symm
        | some l => exact congrArg
            (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) (some 0) t) hI
    · intro x t
      cases x with
      | none => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.unary (some 0) t) hJ
      | some k => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.unary (some 0) t) hI
    · intro x t
      cases x with
      | none => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.diagonal (some 0) t) hJ
      | some k => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.diagonal (some 0) t) hI
  · intro x y
    cases x with
    | none =>
      cases y with
      | none => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) (some 0)) hJ
      | some k => exact hNew.2.2.trans hOld.2.2.symm
    | some k =>
      cases y with
      | none => exact hNew.2.1.trans hOld.2.1.symm
      | some l => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) (some 0)) hI

/-- Arbitrary distinct retained ordinary coordinates preserve their
entire induced L+ record. In particular F cannot create an L-edge
between two retained old vertices that were non-adjacent. -/
theorem shapeMap_preserves_ordinary_pair
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) (i j : Nat)
    (hij : i < j) (hj : j < LevelTree.lev u) :
    ∃ (hI : kptShapeLevelMap family F i < LevelTree.lev (F u))
      (hJ : kptShapeLevelMap family F j < LevelTree.lev (F u)),
      (F u).1.2.ordinaryPair ⟨kptShapeLevelMap family F i, hI⟩
          ⟨kptShapeLevelMap family F j, hJ⟩ =
        u.1.2.ordinaryPair ⟨i, hij.trans hj⟩ ⟨j, hj⟩ := by
  let a := LevelTree.ancestor u j (Nat.le_of_lt hj)
  let b := LevelTree.ancestor u (j+1) (Nat.succ_le_iff.mpr hj)
  have ha : LevelTree.lev a = j := LevelTree.level_ancestor u j (Nat.le_of_lt hj)
  have hb : b ≤ u := LevelTree.ancestor_le u (j+1) (Nat.succ_le_iff.mpr hj)
  have hFa : LevelTree.lev (F a) = kptShapeLevelMap family F j := by
    simpa only [ha] using (kptShapeLevelMap_eq family F a).symm
  obtain ⟨p, c, d, hSource, hMapped, hBelow⟩ := F.preserves_decomposition u j hj
  have hSource' : (admissibleKptSTree family).succ a p c = some b := hSource
  by_cases hInside : ∃ v, v ∈ p ∧ i < LevelTree.lev v
  · obtain ⟨v, hv, hi⟩ := hInside
    obtain ⟨hOldI, hOldJ, hNewI, hNewJ, hPair⟩ :=
      shapeMap_preserves_ordinary_pair_in_parameter family F hSource' hb v hv i hi
    have hPair' : ∃ (hI : kptShapeLevelMap family F i < LevelTree.lev (F u))
        (hJ : LevelTree.lev (F a) < LevelTree.lev (F u)),
        (F u).1.2.ordinaryPair ⟨kptShapeLevelMap family F i, hI⟩
            ⟨LevelTree.lev (F a), hJ⟩ =
          u.1.2.ordinaryPair ⟨i, hOldI⟩ ⟨LevelTree.lev a, hOldJ⟩ :=
      ⟨hNewI, hNewJ, hPair⟩
    simpa only [ha, hFa] using hPair'
  · have hBeyond : ∀ v, v ∈ p → LevelTree.lev v ≤ i := by
      intro v hv
      by_contra hNot
      exact hInside ⟨v, hv, by omega⟩
    obtain ⟨hOldI, hOldJ, hOldEmpty⟩ :=
      canonicalKptStep_empty_cross_after_parameters family
        (canonicalKptSucc_spec family hSource') hb i (by omega) hBeyond
    have hNewBeyond : ∀ v, v ∈ p.map F →
        LevelTree.lev v ≤ kptShapeLevelMap family F i := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      rw [← kptShapeLevelMap_eq family F w]
      exact (kptShapeLevelMap_strictMono family F).monotone (hBeyond w hw)
    have hNewLess : kptShapeLevelMap family F i < LevelTree.lev (F a) := by
      rw [hFa]
      exact kptShapeLevelMap_strictMono family F hij
    have hMapped' : (admissibleKptSTree family).succ (F a) (p.map F) c = some d := hMapped
    obtain ⟨hNewI, hNewJ, hNewEmpty⟩ :=
      canonicalKptStep_empty_cross_after_parameters family
        (canonicalKptSucc_spec family hMapped') hBelow
        (kptShapeLevelMap family F i) hNewLess hNewBeyond
    obtain ⟨hI, hIPair⟩ := shapeMap_preserves_type_pair_at_levelMap family F u i (hij.trans hj)
    obtain ⟨hJ, hJPair⟩ := shapeMap_preserves_type_pair_at_levelMap family F u j hj
    refine ⟨hI, hJ, ?_⟩
    apply ordinaryPair_eq_of_empty_cross u.1.2 (F u).1.2
      ⟨i, hij.trans hj⟩ ⟨j, hj⟩
      ⟨kptShapeLevelMap family F i, hI⟩ ⟨kptShapeLevelMap family F j, hJ⟩
      hIPair hJPair
    · simpa only [ha] using hOldEmpty
    · simpa only [hFa] using hNewEmpty

end SuccessorTree.V10
