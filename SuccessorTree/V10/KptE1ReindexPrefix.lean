import SuccessorTree.V10.KptE1OldPrefixGeometry
import SuccessorTree.V10.KptE1ShapeLevelCut
import SuccessorTree.V10.ShapeMapFullRecovery
import Mathlib.Tactic

/-!
# Retained-coordinate reindexing commutes with the old Kpt predecessor

A genuine one-step target type Q at level ell+1 has predecessor
Q.restrict ell. Pulling Q back to the source coordinates including
the new last ordinary vertex, then restricting to the old n vertices,
must be the SAME complete L+ record as first taking the target old
predecessor and then retaining just the source old levels.

This is a literal identity of all L, E, true and false atomic tables,
not merely an induced embedding. It uses the previously verified
PartialTypeWithE.reindexOrdinary API without a compatibility shim.

The real shape-level retained indices automatically satisfy the
needed commutation equation. The next step identifies the restricted
target predecessor with the ACTUAL image of the source predecessor,
then applies shapeMap_recovers_complete_record to recover its
literal original L+ type.
-/

namespace SuccessorTree.V10

/-- Full reindexing commutes with predecessor restriction whenever
the enlarged index map agrees with the old one on every OLD
coordinate. No E1, shape-map or admissibility assumption. -/
theorem PartialTypeWithE.reindexOrdinary_restrict_last
    {n ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (rho : Fin n → Fin ell)
    (rhoPlus : Fin (n + 1) → Fin (ell + 1))
    (hCompat : ∀ i : Fin n,
      rhoPlus i.castSucc = (rho i).castSucc) :
    (Q.reindexOrdinary rhoPlus).restrict (Nat.le_succ n) =
      (Q.restrict (Nat.le_succ ell)).reindexOrdinary rho := by
  have hCoordinate (x : Option (Fin n)) :
      (liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus =
        liftTypeCoordinate (Nat.le_succ ell) (x.map rho) := by
    cases x with
    | none => rfl
    | some i =>
        change some (rhoPlus i.castSucc) =
          some ((rho i).castSucc)
        exact congrArg some (hCompat i)
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      change Q.lReduct.binary
          ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus)
          ((liftTypeCoordinate (Nat.le_succ n) y).map rhoPlus) r =
        Q.lReduct.binary
          (liftTypeCoordinate (Nat.le_succ ell) (x.map rho))
          (liftTypeCoordinate (Nat.le_succ ell) (y.map rho)) r
      rw [hCoordinate x, hCoordinate y]
    · intro x r
      change Q.lReduct.unary
          ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus) r =
        Q.lReduct.unary
          (liftTypeCoordinate (Nat.le_succ ell) (x.map rho)) r
      rw [hCoordinate x]
    · intro x r
      change Q.lReduct.diagonal
          ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus) r =
        Q.lReduct.diagonal
          (liftTypeCoordinate (Nat.le_succ ell) (x.map rho)) r
      rw [hCoordinate x]
  · intro x y
    change Q.eRelation
        ((liftTypeCoordinate (Nat.le_succ n) x).map rhoPlus)
        ((liftTypeCoordinate (Nat.le_succ n) y).map rhoPlus) =
      Q.eRelation
        (liftTypeCoordinate (Nat.le_succ ell) (x.map rho))
        (liftTypeCoordinate (Nat.le_succ ell) (y.map rho))
    rw [hCoordinate x, hCoordinate y]

/-- Retained old source indices inside the old target predecessor,
using the ACTUAL strict level map. -/
noncomputable def kptShapeOldRetainedIndex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) :
    Fin n → Fin (kptShapeLevelMap family F n) :=
  fun i =>
    ⟨kptShapeLevelMap family F i.val,
      (kptShapeLevelMap_strictMono family F) i.isLt⟩

/-- The genuine enlarged retained index is precisely the
one-coordinate extension of the old index. -/
theorem kptShapeRetainedIndices_compatible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat) (i : Fin n) :
    kptShapeLastRetainedIndex family F n i.castSucc =
      (kptShapeOldRetainedIndex family F n i).castSucc := by
  apply Fin.ext
  rfl

/-- A target successor's complete pulled-back old type is the
literal retained-coordinate pullback of its target predecessor. -/
theorem kptShapeReindex_restrict_last
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd) :
    (Q.reindexOrdinary
        (kptShapeLastRetainedIndex family F n)).restrict
          (Nat.le_succ n) =
      (Q.restrict (Nat.le_succ (kptShapeLevelMap family F n))).
        reindexOrdinary (kptShapeOldRetainedIndex family F n) := by
  exact Q.reindexOrdinary_restrict_last
    (kptShapeOldRetainedIndex family F n)
    (kptShapeLastRetainedIndex family F n)
    (kptShapeRetainedIndices_compatible family F n)


/-- The terminal Sigma letter is literally unchanged by an
ordinary-coordinate reindexing fixing the new last coordinate.
This includes the last-to-type and type-to-last binary/E atoms,
unary/diagonal bits, and all negative atomic facts. -/
theorem PartialTypeWithE.reindexOrdinary_terminalLetter
    {n ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (rho : Fin (n + 1) → Fin (ell + 1))
    (hLast : rho (Fin.last n) = Fin.last ell) :
    (Q.reindexOrdinary rho).terminalLetter = Q.terminalLetter := by
  have hCoordinate (x : Option (Fin 1)) :
      (terminalCoordinate n x).map rho = terminalCoordinate ell x := by
    cases x with
    | none => rfl
    | some i =>
        change some (rho (Fin.last n)) = some (Fin.last ell)
        exact congrArg some hLast
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      change Q.lReduct.binary
          ((terminalCoordinate n x).map rho)
          ((terminalCoordinate n y).map rho) r =
        Q.lReduct.binary
          (terminalCoordinate ell x)
          (terminalCoordinate ell y) r
      rw [hCoordinate x, hCoordinate y]
    · intro x r
      change Q.lReduct.unary
          ((terminalCoordinate n x).map rho) r =
        Q.lReduct.unary (terminalCoordinate ell x) r
      rw [hCoordinate x]
    · intro x r
      change Q.lReduct.diagonal
          ((terminalCoordinate n x).map rho) r =
        Q.lReduct.diagonal (terminalCoordinate ell x) r
      rw [hCoordinate x]
  · intro x y
    change Q.eRelation
        ((terminalCoordinate n x).map rho)
        ((terminalCoordinate n y).map rho) =
      Q.eRelation
        (terminalCoordinate ell x)
        (terminalCoordinate ell y)
    rw [hCoordinate x, hCoordinate y]

/-- The actual strict Kpt shape-level map automatically fixes the
last ordinary vertex, so pulling back a genuine target successor
does NOT change its admissible terminal Sigma letter. -/
theorem kptShapeReindex_terminalLetter
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (n : Nat)
    (Q : PartialTypeWithE
      (kptShapeLevelMap family F n + 1) db du dd) :
    (Q.reindexOrdinary
      (kptShapeLastRetainedIndex family F n)).terminalLetter =
      Q.terminalLetter := by
  exact Q.reindexOrdinary_terminalLetter
    (kptShapeLastRetainedIndex family F n)
    (kptShapeLastRetainedIndex_last family F n)


/-- The actual image-level version of the retained coordinate map.
Using the level of F(a), rather than an externally chosen target
height, avoids dependent casts when reading a target canonical
successor's literal predecessor. -/
noncomputable def kptShapeLastIndexAtNode
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family) :
    Fin (a.1.1 + 1) → Fin ((F a).1.1 + 1) :=
  fun i =>
    ⟨kptShapeLevelMap family F i.val, by
      have hi : i.val ≤ a.1.1 := by omega
      have hmon := (kptShapeLevelMap_strictMono family F).monotone hi
      have hLevel := kptShapeLevelMap_eq family F a
      omega⟩

/-- On the old coordinates this is *exactly* the existing
retainedSocleIndex used by the verified full-record recovery theorem. -/
theorem kptShapeLastIndexAtNode_compatible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family)
    (i : Fin a.1.1) :
    kptShapeLastIndexAtNode family F a i.castSucc =
      (retainedSocleIndex family F a i).castSucc := by
  apply Fin.ext
  rfl

/-- The new last ordinary vertex maps to the last ordinary
coordinate of the real image of this exact source predecessor. -/
theorem kptShapeLastIndexAtNode_last
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family) :
    kptShapeLastIndexAtNode family F a (Fin.last a.1.1) =
      Fin.last (F a).1.1 := by
  apply Fin.ext
  change kptShapeLevelMap family F a.1.1 = (F a).1.1
  exact kptShapeLevelMap_eq family F a

/-- The new source type obtained from a GENUINE target successor
restricts literally to the old source a, provided the target
successor's old restriction is literally F(a), as the canonical
Kpt successor graph itself guarantees. -/
theorem kptShapeReindex_recovers_old_predecessor
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family)
    (Q : PartialTypeWithE ((F a).1.1 + 1) db du dd)
    (hTargetPred :
      Q.restrict (Nat.le_succ (F a).1.1) = (F a).1.2) :
    (Q.reindexOrdinary
      (kptShapeLastIndexAtNode family F a)).restrict
        (Nat.le_succ a.1.1) = a.1.2 := by
  rw [Q.reindexOrdinary_restrict_last
    (retainedSocleIndex family F a)
    (kptShapeLastIndexAtNode family F a)
    (kptShapeLastIndexAtNode_compatible family F a)]
  rw [hTargetPred]
  change shapeMapRetainedRecord family F a = a.1.2
  exact shapeMap_recovers_complete_record family F a

/-- This exact-node retained embedding also preserves the
complete terminal Sigma letter, so the source does not need to
choose an unrelated raw or admissible letter. -/
theorem kptShapeReindex_terminalLetter_atNode
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a : AdmissibleKptNode family)
    (Q : PartialTypeWithE ((F a).1.1 + 1) db du dd) :
    (Q.reindexOrdinary
      (kptShapeLastIndexAtNode family F a)).terminalLetter =
      Q.terminalLetter := by
  exact Q.reindexOrdinary_terminalLetter
    (kptShapeLastIndexAtNode family F a)
    (kptShapeLastIndexAtNode_last family F a)


/-- Genuine Kpt admissibility also fixes all auxiliary E atoms
touching the distinguished type vertex: its entire ordinary socle
is linked TO the type vertex, never from it, and the loop is absent.
These are theorems of its actual partial-structure witness, not
separate E1 assumptions. -/
theorem PartialTypeWithE.admissible_typeESocle
    {m db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE m db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨m,T⟩ : RawPartialTypeNode db du dd)) :
    (∀ i : Fin m, T.eRelation (some i) none = true) ∧
    (∀ i : Fin m, T.eRelation none (some i) = false) ∧
    T.eRelation none none = false := by
  obtain ⟨A,v,hv,hAvoid,hRaw⟩ := hAd
  have hCut : m = A.freeLevel v := by
    have hh := congrArg Sigma.fst hRaw
    exact hh
  have hRecord : T = A.partialTypeAt m v := by
    have hSigma :
        (⟨m,T⟩ : RawPartialTypeNode db du dd) =
          (⟨m,A.partialTypeAt m v⟩ :
            RawPartialTypeNode db du dd) := by
      calc
        (⟨m,T⟩ : RawPartialTypeNode db du dd) =
            A.rawTypeAtFree v := hRaw
        _ = (⟨m,A.partialTypeAt m v⟩ :
              RawPartialTypeNode db du dd) := by
          change
            (⟨A.freeLevel v,
              A.partialTypeAt (A.freeLevel v) v⟩ :
              RawPartialTypeNode db du dd) =
            (⟨m,A.partialTypeAt m v⟩ :
              RawPartialTypeNode db du dd)
          rw [←hCut]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hRecord]
    exact A.partialTypeAt_fullESocle m v (by omega) i
  · intro i
    rw [hRecord]
    exact A.partialTypeAt_no_reverseE m v (by omega) i
  · rw [hRecord]
    exact A.partialTypeAt_no_typeE_loop m v

/-- Retaining any genuine subset of ordinary coordinates therefore
preserves all three canonical distinguished-type E conditions.
This includes the last source successor coordinate under the
actual shape-level retained map. -/
theorem PartialTypeWithE.reindexOrdinary_typeESocle
    {n m db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE m db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨m,T⟩ : RawPartialTypeNode db du dd))
    (rho : Fin n → Fin m) :
    (∀ i : Fin n,
      (T.reindexOrdinary rho).eRelation (some i) none = true) ∧
    (∀ i : Fin n,
      (T.reindexOrdinary rho).eRelation none (some i) = false) ∧
    (T.reindexOrdinary rho).eRelation none none = false := by
  obtain ⟨hFor,hBack,hLoop⟩ :=
    T.admissible_typeESocle family hAd
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change T.eRelation (some (rho i)) none = true
    exact hFor (rho i)
  · intro i
    change T.eRelation none (some (rho i)) = false
    exact hBack (rho i)
  · exact hLoop

end SuccessorTree.V10
