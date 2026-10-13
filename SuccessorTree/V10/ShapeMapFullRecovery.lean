import SuccessorTree.V10.ShapeMapOrdinaryRecovery
import Mathlib.Tactic

/-!
# Recover a complete source type on the retained coordinates

The pullback of F(u) along the strictly increasing image-level map,
with the distinguished type vertex fixed, is exactly u. The statement
includes all directed binary, singleton, diagonal and auxiliary E atoms.

The type singleton at level zero follows from the root extension law;
ordinary-type pairs and ordinary-ordinary pairs follow from the actual
successor and parameter transport. No age-preservation or M2 assumption
is used.
-/

namespace SuccessorTree.V10

/-- An initial-socle restriction leaves the type singleton unchanged. -/
theorem rawPrefix_preserves_type_singleton {db du dd : Nat}
    {a b : RawPartialTypeNode db du dd} (hab : a ≤ b) :
    b.2.restrict (Nat.zero_le b.1) = a.2.restrict (Nat.zero_le a.1) := by
  rw [hab.2, PartialTypeWithE.restrict_trans]

/-- Root extension is sufficient; this holds even when F does not
fix root levels. -/
theorem shapeMap_preserves_type_singleton {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) :
    (F u).1.2.restrict (Nat.zero_le (F u).1.1) =
      u.1.2.restrict (Nat.zero_le u.1.1) := by
  let r := LevelTree.ancestor u 0 (Nat.zero_le _)
  have hr : LevelTree.lev r = 0 := LevelTree.level_ancestor u 0 (Nat.zero_le _)
  have hru : r ≤ u := LevelTree.ancestor_le u 0 (Nat.zero_le _)
  have hrFu : r ≤ F u := le_trans (F.root_le' hr) (F.map_le_of_le hru)
  exact (rawPrefix_preserves_type_singleton hrFu).trans
    (rawPrefix_preserves_type_singleton hru).symm

/-- The retained coordinate of the source socle. -/
noncomputable def retainedSocleIndex {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) (i : Fin u.1.1) : Fin (F u).1.1 :=
  ⟨kptShapeLevelMap family F i.val, by
    change kptShapeLevelMap family F i.val < LevelTree.lev (F u)
    rw [← kptShapeLevelMap_eq family F u]
    exact kptShapeLevelMap_strictMono family F i.isLt⟩

/-- Pull back the ENTIRE image record, keeping the type vertex. -/
noncomputable def shapeMapRetainedRecord {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) : PartialTypeWithE u.1.1 db du dd :=
  let coordinate := Option.map (retainedSocleIndex family F u)
  { lReduct :=
      { binary := fun x y t => (F u).1.2.lReduct.binary (coordinate x) (coordinate y) t
        unary := fun x t => (F u).1.2.lReduct.unary (coordinate x) t
        diagonal := fun x t => (F u).1.2.lReduct.diagonal (coordinate x) t }
    eRelation := fun x y => (F u).1.2.eRelation (coordinate x) (coordinate y) }

/-- Full record recovery, including negative atoms and ordinary E.
This is the concrete normalized content of the draft's recovery claim. -/
theorem shapeMap_recovers_complete_record {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (u : AdmissibleKptNode family) :
    shapeMapRetainedRecord family F u = u.1.2 := by
  let index := retainedSocleIndex family F u
  have hSingleton := shapeMap_preserves_type_singleton family F u
  have hPair (i : Fin u.1.1) :
      (F u).1.2.pairAt (index i).val (index i).isLt =
        u.1.2.pairAt i.val i.isLt := by
    obtain ⟨h, hPair⟩ := shapeMap_preserves_type_pair_at_levelMap family F u i.val i.isLt
    exact hPair
  have hOrdinary (i j : Fin u.1.1) :
      (∀ t : Fin db,
        (F u).1.2.lReduct.binary (some (index i)) (some (index j)) t =
          u.1.2.lReduct.binary (some i) (some j) t) ∧
      (F u).1.2.eRelation (some (index i)) (some (index j)) =
        u.1.2.eRelation (some i) (some j) := by
    rcases lt_trichotomy i.val j.val with hLess | hEqual | hGreater
    · obtain ⟨hi, hj, h⟩ :=
        shapeMap_preserves_ordinary_pair family F u i.val j.val hLess j.isLt
      exact ⟨fun t => congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) none t) h,
        congrArg (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) none) h⟩
    · have hij : i = j := Fin.ext hEqual
      subst j
      exact ⟨fun t => congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) (some 0) t) (hPair i),
        congrArg (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) (some 0)) (hPair i)⟩
    · obtain ⟨hj, hi, h⟩ :=
        shapeMap_preserves_ordinary_pair family F u j.val i.val hGreater i.isLt
      exact ⟨fun t => congrArg
        (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary none (some 0) t) h,
        congrArg (fun P : PartialTypeWithE 1 db du dd => P.eRelation none (some 0)) h⟩
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x with
      | none =>
        cases y with
        | none => exact congrArg
            (fun P : PartialTypeWithE 0 db du dd => P.lReduct.binary none none t) hSingleton
        | some j => exact congrArg
            (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary none (some 0) t) (hPair j)
      | some i =>
        cases y with
        | none => exact congrArg
            (fun P : PartialTypeWithE 1 db du dd => P.lReduct.binary (some 0) none t) (hPair i)
        | some j => exact (hOrdinary i j).1 t
    · intro x t
      cases x with
      | none => exact congrArg
          (fun P : PartialTypeWithE 0 db du dd => P.lReduct.unary none t) hSingleton
      | some i => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.unary (some 0) t) (hPair i)
    · intro x t
      cases x with
      | none => exact congrArg
          (fun P : PartialTypeWithE 0 db du dd => P.lReduct.diagonal none t) hSingleton
      | some i => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.lReduct.diagonal (some 0) t) (hPair i)
  · intro x y
    cases x with
    | none =>
      cases y with
      | none => exact congrArg
          (fun P : PartialTypeWithE 0 db du dd => P.eRelation none none) hSingleton
      | some j => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.eRelation none (some 0)) (hPair j)
    | some i =>
      cases y with
      | none => exact congrArg
          (fun P : PartialTypeWithE 1 db du dd => P.eRelation (some 0) none) (hPair i)
      | some j => exact (hOrdinary i j).2

end SuccessorTree.V10
