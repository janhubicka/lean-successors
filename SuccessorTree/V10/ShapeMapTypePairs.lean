import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# Every genuine Kpt ShapeMap preserves retained two-vertex records

At the target level corresponding to source coordinate i, the pair
consisting of i and the distinguished type vertex carries the same
complete L+ record. This is derived from the actual weak successor
law, using its genuine successor below F(a), not equality with F(a).
No M2 axiom, B3 condition or abstract preservation interface is used.
-/

namespace SuccessorTree.V10

/-- Retain a chosen ordinary coordinate and the distinguished type vertex. -/
def pairCoordinate {n : Nat} (i : Nat) (hi : i < n) :
    Option (Fin 1) → Option (Fin n)
  | none => none
  | some _ => some ⟨i,hi⟩

def PartialTypeWithE.pairAt {n db du dd : Nat}
    (Q : PartialTypeWithE n db du dd) (i : Nat) (hi : i < n) :
    PartialTypeWithE 1 db du dd where
  lReduct :=
    { binary := fun x y t =>
        Q.lReduct.binary (pairCoordinate i hi x) (pairCoordinate i hi y) t
      unary := fun x t => Q.lReduct.unary (pairCoordinate i hi x) t
      diagonal := fun x t => Q.lReduct.diagonal (pairCoordinate i hi x) t }
  eRelation := fun x y => Q.eRelation (pairCoordinate i hi x) (pairCoordinate i hi y)

/-- Full pair extraction commutes with the actual induced prefix. -/
theorem PartialTypeWithE.pairAt_restrict {n m db du dd : Nat}
    (Q : PartialTypeWithE m db du dd) (hn : n ≤ m)
    (i : Nat) (hi : i < n) :
    (Q.restrict hn).pairAt i hi = Q.pairAt i (lt_of_lt_of_le hi hn) := by
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

/-- The terminal Sigma letter is exactly the pair at the new coordinate. -/
theorem PartialTypeWithE.pairAt_last {ell db du dd : Nat}
    (Q : PartialTypeWithE (ell+1) db du dd) :
    Q.pairAt ell (Nat.lt_succ_self ell) = Q.terminalLetter := by
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

/-- A canonical successor below an upper node places its full terminal
letter at the predecessor's coordinate in the upper node. -/
theorem canonicalKptStep_letter_in_upper {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {a b u : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : RawKptLetter db du dd}
    (hStep : IsCanonicalKptStep family a p c b) (hBelow : b ≤ u) :
    ∃ h : LevelTree.lev a < LevelTree.lev u,
      u.1.2.pairAt (LevelTree.lev a) h = c := by
  obtain ⟨ell,f,hf,Q,hA,hB,hC,_hValid,_hParam,_hGate⟩ := hStep
  have hLevel : LevelTree.lev a = ell := congrArg Sigma.fst hA
  have hPrefix :
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) ≤ u.1 := by
    rw [←hB]
    exact hBelow
  obtain ⟨hLe,hQ⟩ := hPrefix
  change ell+1 ≤ u.1.1 at hLe
  rw [hLevel]
  refine ⟨by change ell < u.1.1; omega, ?_⟩
  rw [hC,←Q.pairAt_last]
  calc
    u.1.2.pairAt ell (by omega) =
        (u.1.2.restrict hLe).pairAt ell (Nat.lt_succ_self ell) :=
      (u.1.2.pairAt_restrict hLe ell (Nat.lt_succ_self ell)).symm
    _ = Q.pairAt ell (Nat.lt_succ_self ell) := by rw [←hQ]

/-- An arbitrary genuine ShapeMap retains the full two-vertex L+
record at every source coordinate. In particular it retains every
unary and diagonal fact and every directed link to the type vertex. -/
theorem shapeMap_preserves_type_pair {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) (i : Nat) (hi : i < LevelTree.lev u) :
    let a := LevelTree.ancestor u i (Nat.le_of_lt hi)
    ∃ h : LevelTree.lev (F a) < LevelTree.lev (F u),
      (F u).1.2.pairAt (LevelTree.lev (F a)) h = u.1.2.pairAt i hi := by
  let a := LevelTree.ancestor u i (Nat.le_of_lt hi)
  let b := LevelTree.ancestor u (i+1) (Nat.succ_le_iff.mpr hi)
  obtain ⟨p,c,d,hSource,hMapped,hBelow⟩ := F.preserves_decomposition u i hi
  have hSourceStep : IsCanonicalKptStep family a p c.1 b := by
    apply canonicalKptSucc_spec family
    exact hSource
  have hMappedStep : IsCanonicalKptStep family (F a) (p.map F) c.1 d := by
    apply canonicalKptSucc_spec family
    exact hMapped
  obtain ⟨hOld,hOldPair⟩ := canonicalKptStep_letter_in_upper family
    hSourceStep (LevelTree.ancestor_le u (i+1) (Nat.succ_le_iff.mpr hi))
  have ha : LevelTree.lev a = i := LevelTree.level_ancestor u i (Nat.le_of_lt hi)
  have hPair : u.1.2.pairAt i hi = c.1 := by
    simpa only [ha] using hOldPair
  obtain ⟨hNew,hNewPair⟩ := canonicalKptStep_letter_in_upper family hMappedStep hBelow
  exact ⟨hNew,hNewPair.trans hPair.symm⟩

end SuccessorTree.V10
