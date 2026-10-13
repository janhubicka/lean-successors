import SuccessorTree.V10.ShapeMapTypePairs
import Mathlib.Tactic

/-!
# Full ordinary-vertex parameter records inside ShapeMap images

A real canonical parameter is not merely compatible with the output:
its complete L+ record occurs at the new ordinary vertex, over the
parameter's own initial socle. The same holds after applying an
arbitrary ShapeMap, because its weak successor has the mapped parameter
list and lies below the image of the whole type.

This is the exact transport needed for the padded source witnesses.
It is derived from genuine successor graphs, without M2 or B3.
-/

namespace SuccessorTree.V10

/-- Rename a selected ordinary vertex to the type vertex and retain
a chosen initial socle. -/
def ordinaryTypeCoordinate {n f : Nat}
    (j : Nat) (hj : j < n) (hf : f ≤ n) :
    Option (Fin f) → Option (Fin n)
  | none => some ⟨j,hj⟩
  | some i => some ⟨i.val,lt_of_lt_of_le i.isLt hf⟩

def PartialTypeWithE.ordinaryType {n db du dd : Nat}
    (Q : PartialTypeWithE n db du dd)
    (j : Nat) (hj : j < n) (f : Nat) (hf : f ≤ n) :
    PartialTypeWithE f db du dd where
  lReduct :=
    { binary := fun x y t => Q.lReduct.binary
        (ordinaryTypeCoordinate j hj hf x) (ordinaryTypeCoordinate j hj hf y) t
      unary := fun x t => Q.lReduct.unary (ordinaryTypeCoordinate j hj hf x) t
      diagonal := fun x t => Q.lReduct.diagonal (ordinaryTypeCoordinate j hj hf x) t }
  eRelation := fun x y => Q.eRelation
    (ordinaryTypeCoordinate j hj hf x) (ordinaryTypeCoordinate j hj hf y)

/-- Taking an ordinary-vertex type commutes with ambient prefix restriction. -/
theorem PartialTypeWithE.ordinaryType_restrict {n m db du dd : Nat}
    (Q : PartialTypeWithE m db du dd) (hn : n ≤ m)
    (j : Nat) (hj : j < n) (f : Nat) (hf : f ≤ n) :
    (Q.restrict hn).ordinaryType j hj f hf =
      Q.ordinaryType j (lt_of_lt_of_le hj hn) f (le_trans hf hn) := by
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

/-- At the final ordinary coordinate this is the actual canonical
parameter extraction used in the definition of the successor. -/
theorem PartialTypeWithE.lastOrdinaryParameter_eq_ordinaryType
    {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell+1) db du dd) (f : Nat) (hf : f ≤ ell) :
    Q.lastOrdinaryParameter f hf =
      Q.ordinaryType ell (Nat.lt_succ_self ell) f (le_trans hf (Nat.le_succ ell)) := by
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

/-- A genuine nonempty canonical parameter occurs as its full record
at the corresponding ordinary vertex in every upper extension. -/
theorem canonicalKptStep_parameter_in_upper {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b u : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) (hBelow : b ≤ u)
    (v : AdmissibleKptNode family) (hv : v ∈ p) :
    ∃ (hj : LevelTree.lev a < LevelTree.lev u)
      (hf : LevelTree.lev v ≤ LevelTree.lev u),
      v.1 = (⟨LevelTree.lev v,
        u.1.2.ordinaryType (LevelTree.lev a) hj (LevelTree.lev v) hf⟩ :
          RawPartialTypeNode db du dd) := by
  obtain ⟨ell,f,hf,Q,hA,hB,_hC,_hValid,hParam,_hGate⟩ := hStep
  have hMem : v.1 ∈ p.map (fun x => x.1) := List.mem_map.mpr ⟨v,hv,rfl⟩
  rw [hParam] at hMem
  have hPos : f ≠ 0 := by
    intro hz
    simp [PartialTypeWithE.canonicalParameterRecord,hz] at hMem
  have hV : v.1 = (⟨f,Q.lastOrdinaryParameter f hf⟩ : RawPartialTypeNode db du dd) := by
    simpa [PartialTypeWithE.canonicalParameterRecord,hPos] using hMem
  have hALevel : LevelTree.lev a = ell := congrArg Sigma.fst hA
  have hVLevel : LevelTree.lev v = f := congrArg Sigma.fst hV
  have hPrefix : (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) ≤ u.1 := by
    rw [←hB]
    exact hBelow
  obtain ⟨hLe,hQ⟩ := hPrefix
  change ell+1 ≤ u.1.1 at hLe
  rw [hALevel,hVLevel]
  refine ⟨by change ell < u.1.1; omega,by change f ≤ u.1.1; omega,?_⟩
  rw [hV]
  apply congrArg (fun R : PartialTypeWithE f db du dd =>
    (⟨f,R⟩ : RawPartialTypeNode db du dd))
  calc
    Q.lastOrdinaryParameter f hf =
        Q.ordinaryType ell (Nat.lt_succ_self ell) f (le_trans hf (Nat.le_succ ell)) :=
      Q.lastOrdinaryParameter_eq_ordinaryType f hf
    _ = (u.1.2.restrict hLe).ordinaryType ell (Nat.lt_succ_self ell)
        f (le_trans hf (Nat.le_succ ell)) := by rw [←hQ]
    _ = u.1.2.ordinaryType ell (by omega) f (by omega) :=
      u.1.2.ordinaryType_restrict hLe ell (Nat.lt_succ_self ell)
        f (le_trans hf (Nat.le_succ ell))

/-- The complete image of every actual source parameter is literally
present at the retained ordinary coordinate of F(u). This uses only
the weak-successor law, never a total equality of successor images. -/
theorem shapeMap_transports_parameter_record {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {a b u : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : AdmissibleKptSigma family}
    (hSource : (admissibleKptSTree family).succ a p c = some b)
    (hBelow : b ≤ u)
    (v : AdmissibleKptNode family) (hv : v ∈ p) :
    ∃ (hj : LevelTree.lev (F a) < LevelTree.lev (F u))
      (hf : LevelTree.lev (F v) ≤ LevelTree.lev (F u)),
      (F v).1 = (⟨LevelTree.lev (F v),
        (F u).1.2.ordinaryType (LevelTree.lev (F a)) hj
          (LevelTree.lev (F v)) hf⟩ : RawPartialTypeNode db du dd) := by
  obtain ⟨d,hMapped,hdu⟩ := F.weak_succ' hSource
  have hStep : IsCanonicalKptStep family (F a) (p.map F) c.1 d :=
    canonicalKptSucc_spec family hMapped
  exact canonicalKptStep_parameter_in_upper family hStep
    (hdu.trans (F.map_le_of_le hBelow)) (F v) (List.mem_map.mpr ⟨v,hv,rfl⟩)

end SuccessorTree.V10
