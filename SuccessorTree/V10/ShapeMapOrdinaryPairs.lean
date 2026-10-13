import SuccessorTree.V10.ShapeMapParameterTransport
import SuccessorTree.V10.LevelRemovalSkipsOnly
import Mathlib.Tactic

/-!
# Full ordinary-ordinary pair transport through actual canonical parameters

At every coordinate inside the free socle of an actual parameter, the
ordinary-ordinary pair is the type pair of that parameter. Apply the
already proved type-pair preservation to the parameter, then place its
full image back inside the image of the ambient type. All L+ atoms,
including negative binary facts, both directions and singleton data,
are retained. The image successor is only required to lie below F(u).

This is the pair transport needed between the real vertices of the
non-edge-padded source witness. Beyond a parameter's free cut, the
separate no-new-tuples argument is still needed for full recovery.
-/

namespace SuccessorTree.V10

/-- Retain two ordinary vertices, with the second renamed to the
new distinguished vertex. No age or E information is discarded. -/
def PartialTypeWithE.ordinaryPair {n db du dd : Nat}
    (Q : PartialTypeWithE n db du dd) (i j : Fin n) :
    PartialTypeWithE 1 db du dd :=
  let coordinate : Option (Fin 1) → Option (Fin n) :=
    fun x => match x with | none => some j | some _ => some i
  { lReduct :=
      { binary := fun x y t => Q.lReduct.binary (coordinate x) (coordinate y) t
        unary := fun x t => Q.lReduct.unary (coordinate x) t
        diagonal := fun x t => Q.lReduct.diagonal (coordinate x) t }
    eRelation := fun x y => Q.eRelation (coordinate x) (coordinate y) }

/-- Extracting a parameter and then one of its type pairs is the
same complete ordinary pair in the ambient record. -/
theorem PartialTypeWithE.ordinaryType_pairAt {n db du dd : Nat}
    (Q : PartialTypeWithE n db du dd)
    (j : Nat) (hj : j < n) (f : Nat) (hf : f ≤ n)
    (i : Nat) (hi : i < f) :
    (Q.ordinaryType j hj f hf).pairAt i hi =
      Q.ordinaryPair ⟨i, lt_of_lt_of_le hi hf⟩ ⟨j, hj⟩ := by
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

/-- Express retained coordinates using the total level map, avoiding
any dependence on which source-level representative was selected. -/
theorem shapeMap_preserves_type_pair_at_levelMap {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) (i : Nat) (hi : i < LevelTree.lev u) :
    ∃ h : kptShapeLevelMap family F i < LevelTree.lev (F u),
      (F u).1.2.pairAt (kptShapeLevelMap family F i) h = u.1.2.pairAt i hi := by
  let a := LevelTree.ancestor u i (Nat.le_of_lt hi)
  have ha : LevelTree.lev a = i :=
    LevelTree.level_ancestor u i (Nat.le_of_lt hi)
  have hImageLevel : LevelTree.lev (F a) = kptShapeLevelMap family F i := by
    simpa only [ha] using (kptShapeLevelMap_eq family F a).symm
  obtain ⟨h, hPair⟩ := shapeMap_preserves_type_pair family F u i hi
  change ∃ h : kptShapeLevelMap family F i < (F u).1.1,
    (F u).1.2.pairAt (kptShapeLevelMap family F i) h = u.1.2.pairAt i hi
  have hPair' : ∃ h : LevelTree.lev (F a) < LevelTree.lev (F u),
      (F u).1.2.pairAt (LevelTree.lev (F a)) h = u.1.2.pairAt i hi :=
    ⟨h, hPair⟩
  simpa only [hImageLevel] using hPair'

/-- Full induced pair preservation between a retained ordinary
coordinate and the vertex introduced with an actual parameter whose
free socle contains that coordinate. This is derived for arbitrary F,
not postulated as an age-preservation or compatibility premise. -/
theorem shapeMap_preserves_ordinary_pair_in_parameter
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {a b u : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : AdmissibleKptSigma family}
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (hBelow : b ≤ u) (v : AdmissibleKptNode family) (hv : v ∈ p)
    (i : Nat) (hi : i < LevelTree.lev v) :
    ∃ (hOldI : i < LevelTree.lev u)
      (hOldJ : LevelTree.lev a < LevelTree.lev u)
      (hNewI : kptShapeLevelMap family F i < LevelTree.lev (F u))
      (hNewJ : LevelTree.lev (F a) < LevelTree.lev (F u)),
      (F u).1.2.ordinaryPair ⟨kptShapeLevelMap family F i, hNewI⟩
          ⟨LevelTree.lev (F a), hNewJ⟩ =
        u.1.2.ordinaryPair ⟨i, hOldI⟩ ⟨LevelTree.lev a, hOldJ⟩ := by
  obtain ⟨hOldJ, hOldF, hOldRaw⟩ := canonicalKptStep_parameter_in_upper family
    (canonicalKptSucc_spec family hSucc) hBelow v hv
  obtain ⟨hNewJ, hNewF, hNewRaw⟩ :=
    shapeMap_transports_parameter_record family F hSucc hBelow v hv
  have hOldRecord : v.1.2 = u.1.2.ordinaryType (LevelTree.lev a) hOldJ
      (LevelTree.lev v) hOldF := eq_of_heq (Sigma.mk.inj_iff.mp hOldRaw).2
  have hNewRecord : (F v).1.2 = (F u).1.2.ordinaryType
      (LevelTree.lev (F a)) hNewJ (LevelTree.lev (F v)) hNewF :=
    eq_of_heq (Sigma.mk.inj_iff.mp hNewRaw).2
  obtain ⟨hIn, hPair⟩ := shapeMap_preserves_type_pair_at_levelMap family F v i hi
  refine ⟨lt_of_lt_of_le hi hOldF, hOldJ,
    lt_of_lt_of_le hIn hNewF, hNewJ, ?_⟩
  rw [hNewRecord, hOldRecord, PartialTypeWithE.ordinaryType_pairAt,
    PartialTypeWithE.ordinaryType_pairAt] at hPair
  exact hPair

end SuccessorTree.V10
