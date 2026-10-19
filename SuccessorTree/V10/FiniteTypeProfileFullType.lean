import SuccessorTree.V10.FiniteTypeProfileRecovery
import SuccessorTree.V10.CanonicalCrossing

/-!
# Ordinary full-type equality under finite profile maps

The actual partial type is the full L+ type at its free cut. Above that cut
the no-new-tuples law fixes all remaining earlier incidences. Together with
finite prefix transport, this proves ordinary type-respecting behavior.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

/-- A full type through a cut detects any free level strictly below that
cut. The auxiliary E column is essential to this assertion. -/
theorem freeLevel_eq_of_partialTypeAt_eq_of_lt
    (A : EnumeratedPartialStructure db du dd) (i v w : Nat)
    (hType : A.partialTypeAt i v = A.partialTypeAt i w)
    (hSmall : A.freeLevel v < i) : A.freeLevel v = A.freeLevel w := by
  have hE (x : Nat) (hx : x < i) : A.E x v = A.E x w :=
    congrArg (fun Q : PartialTypeWithE i db du dd =>
      Q.eRelation (some ⟨x, hx⟩) none) hType
  have hLe : A.freeLevel w ≤ A.freeLevel v := by
    by_contra hNot
    have hTrue : A.E (A.freeLevel v) w = true :=
      (A.E_iff_freeLevel _ _).2 (by omega)
    have hFalse := (hE (A.freeLevel v) hSmall).symm.trans (A.freeLevel_firstMissing v)
    rw [hTrue] at hFalse
    contradiction
  apply Nat.le_antisymm _ hLe
  by_contra hNot
  have hTrue : A.E (A.freeLevel w) v = true :=
    (A.E_iff_freeLevel _ _).2 (by omega)
  have hFalse := (hE (A.freeLevel w) (by omega)).trans (A.freeLevel_firstMissing w)
  rw [hTrue] at hFalse
  contradiction

/-- Once actual partial types agree, the complete types agree over every
earlier initial segment. All crossings beyond the common free cut are zero. -/
theorem partialTypeAt_eq_of_rawTypeAtFree_eq
    (A : EnumeratedPartialStructure db du dd) (i v w : Nat)
    (hiv : i ≤ v) (hiw : i ≤ w) (hv : v < A.size) (hw : w < A.size)
    (hRaw : A.rawTypeAtFree v = A.rawTypeAtFree w) :
    A.partialTypeAt i v = A.partialTypeAt i w := by
  have hFree : A.freeLevel v = A.freeLevel w := congrArg Sigma.fst hRaw
  have hRecord : A.partialTypeAt (A.freeLevel v) v =
      A.partialTypeAt (A.freeLevel v) w := by
    have hHEq := (Sigma.mk.inj_iff.mp hRaw).2
    rw [← hFree] at hHEq
    exact eq_of_heq hHEq
  have hCross (x : Fin i) (t : Fin db) :
      A.L.binary x.val v t = A.L.binary x.val w t ∧
        A.L.binary v x.val t = A.L.binary w x.val t := by
    by_cases hx : x.val < A.freeLevel v
    · exact ⟨congrArg (fun Q : PartialTypeWithE (A.freeLevel v) db du dd =>
          Q.lReduct.binary (some ⟨x.val, hx⟩) none t) hRecord,
        congrArg (fun Q : PartialTypeWithE (A.freeLevel v) db du dd =>
          Q.lReduct.binary none (some ⟨x.val, hx⟩) t) hRecord⟩
    · have hV := binary_false_at_or_above_freeLevel A x.val v
        (lt_of_lt_of_le x.isLt hiv) (lt_trans (lt_of_lt_of_le x.isLt hiv) hv)
        hv (by omega) t
      have hW := binary_false_at_or_above_freeLevel A x.val w
        (lt_of_lt_of_le x.isLt hiw) (lt_trans (lt_of_lt_of_le x.isLt hiw) hw)
        hw (by omega) t
      exact ⟨hV.1.trans hW.1.symm, hV.2.trans hW.2.symm⟩
  have hReverse (x : Fin i) : A.E v x.val = false ∧ A.E w x.val = false := by
    constructor
    · cases hE : A.E v x.val with
      | false => rfl
      | true =>
          have hSpacing := A.spaced v x.val hE
          have hLess := lt_of_lt_of_le x.isLt hiv
          omega
    · cases hE : A.E w x.val with
      | false => rfl
      | true =>
          have hSpacing := A.spaced w x.val hE
          have hLess := lt_of_lt_of_le x.isLt hiw
          omega
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x with
      | none =>
          cases y with
          | none => exact congrArg (fun Q : PartialTypeWithE (A.freeLevel v) db du dd =>
              Q.lReduct.binary none none t) hRecord
          | some y => exact (hCross y t).2
      | some x =>
          cases y with
          | none => exact (hCross x t).1
          | some y => rfl
    · intro x t
      cases x with
      | none => exact congrArg (fun Q : PartialTypeWithE (A.freeLevel v) db du dd =>
          Q.lReduct.unary none t) hRecord
      | some x => rfl
    · intro x t
      cases x with
      | none => exact congrArg (fun Q : PartialTypeWithE (A.freeLevel v) db du dd =>
          Q.lReduct.diagonal none t) hRecord
      | some x => rfl
  · intro x y
    cases x with
    | none =>
        cases y with
        | none => exact congrArg (fun Q : PartialTypeWithE (A.freeLevel v) db du dd =>
            Q.eRelation none none) hRecord
        | some y => exact (hReverse y).1.trans (hReverse y).2.symm
    | some x =>
        cases y with
        | none =>
            change A.E x.val v = A.E x.val w
            rw [E_eq_decide_freeLevel, E_eq_decide_freeLevel, hFree]
        | some y => rfl

namespace CoherentTypeProfileMap

variable {A B : FiniteTypeBase family}

/-- Exact full record of a prefix of the image of an actual partial type. -/
theorem vertexType_prefix_record (h : CoherentTypeProfileMap A B)
    (v : Fin A.size) (i : Nat) (hi : i ≤ A.str.freeLevel v.val) :
    (h ((TypeProfile.vertexType A v).ancestor i hi)).1 =
      (⟨h.levelMap i (hi.trans ((A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt))),
        B.str.partialTypeAt
          (h.levelMap i (hi.trans ((A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt))))
          (h.vertexMap v).val⟩ : RawPartialTypeNode db du dd) := by
  let p := (TypeProfile.vertexType A v).ancestor i hi
  have hBelow : h p ≤ (TypeProfile.vertexType B (h.vertexMap v)).1 := by
    rw [← h.vertexType_transport v]
    exact h.prefix p (TypeProfile.vertexType A v)
      ((TypeProfile.vertexType A v).ancestor_le i hi)
  have hBound : (h p).1.1 ≤ B.str.freeLevel (h.vertexMap v).val := hBelow.1
  have hRecord : (h p).1.2 =
      B.str.partialTypeAt (h p).1.1 (h.vertexMap v).val :=
    hBelow.2.trans (B.str.partialTypeAt_restrict (h p).1.1
      (B.str.freeLevel (h.vertexMap v).val) (h.vertexMap v).val hBound)
  calc
    (h p).1 = (⟨(h p).1.1,
        B.str.partialTypeAt (h p).1.1 (h.vertexMap v).val⟩ :
          RawPartialTypeNode db du dd) := congrArg (Sigma.mk _) hRecord
    _ = _ := by
      have hLevel : (h p).1.1 =
          h.levelMap i (hi.trans ((A.str.freeLevel_le v.val).trans (Nat.le_of_lt v.isLt))) :=
        h.levelMap_ancestor (TypeProfile.vertexType A v) i hi
      rw [hLevel]

/-- Finite profile maps are type-respecting on the underlying full L+
structures. Equality includes the auxiliary E relation and all negative bits. -/
theorem preserves_full_type_equality (h : CoherentTypeProfileMap A B)
    (i : Nat) (v w : Fin A.size) (hiv : i ≤ v.val) (hiw : i ≤ w.val)
    (hType : A.str.partialTypeAt i v.val = A.str.partialTypeAt i w.val) :
    B.str.partialTypeAt (h.levelMap i (hiv.trans (Nat.le_of_lt v.isLt)))
        (h.vertexMap v).val =
      B.str.partialTypeAt (h.levelMap i (hiv.trans (Nat.le_of_lt v.isLt)))
        (h.vertexMap w).val := by
  by_cases hFullV : i ≤ A.str.freeLevel v.val
  · have hFullW : i ≤ A.str.freeLevel w.val := by
      by_contra hNot
      have hFree := freeLevel_eq_of_partialTypeAt_eq_of_lt
        A.str i w.val v.val hType.symm (by omega)
      omega
    have hPrefixes :
        (TypeProfile.vertexType A v).ancestor i hFullV =
          (TypeProfile.vertexType A w).ancestor i hFullW := by
      apply Subtype.ext
      apply Subtype.ext
      change (⟨i, (A.str.partialTypeAt (A.str.freeLevel v.val) v.val).restrict hFullV⟩ :
          RawPartialTypeNode db du dd) =
        ⟨i, (A.str.partialTypeAt (A.str.freeLevel w.val) w.val).restrict hFullW⟩
      rw [A.str.partialTypeAt_restrict, A.str.partialTypeAt_restrict, hType]
    have hMapped := congrArg (fun u : TypeProfile A => (h u).1) hPrefixes
    rw [h.vertexType_prefix_record v i hFullV,
      h.vertexType_prefix_record w i hFullW] at hMapped
    exact eq_of_heq (Sigma.mk.inj_iff.mp hMapped).2
  · have hSmall : A.str.freeLevel v.val < i := by omega
    have hFree := freeLevel_eq_of_partialTypeAt_eq_of_lt
      A.str i v.val w.val hType hSmall
    have hShort : A.str.partialTypeAt (A.str.freeLevel v.val) v.val =
        A.str.partialTypeAt (A.str.freeLevel v.val) w.val := by
      have hRestrict := congrArg
        (fun Q : PartialTypeWithE i db du dd => Q.restrict (Nat.le_of_lt hSmall)) hType
      simpa only [A.str.partialTypeAt_restrict] using hRestrict
    have hTypes : TypeProfile.vertexType A v = TypeProfile.vertexType A w := by
      apply Subtype.ext
      apply Subtype.ext
      change (⟨A.str.freeLevel v.val, A.str.partialTypeAt (A.str.freeLevel v.val) v.val⟩ :
          RawPartialTypeNode db du dd) =
        ⟨A.str.freeLevel w.val, A.str.partialTypeAt (A.str.freeLevel w.val) w.val⟩
      rw [← hFree, hShort]
    have hMapped := congrArg (fun u : TypeProfile A => (h u).1) hTypes
    rw [h.vertexType_transport v, h.vertexType_transport w] at hMapped
    exact partialTypeAt_eq_of_rawTypeAtFree_eq B.str
      (h.levelMap i (hiv.trans (Nat.le_of_lt v.isLt)))
      (h.vertexMap v).val (h.vertexMap w).val
      (h.levelMap_mono (hiv.trans (Nat.le_of_lt v.isLt)) (Nat.le_of_lt v.isLt) hiv)
      (h.levelMap_mono (hiw.trans (Nat.le_of_lt w.isLt)) (Nat.le_of_lt w.isLt) hiw)
      (h.vertexMap v).isLt (h.vertexMap w).isLt hMapped

end CoherentTypeProfileMap
end SuccessorTree.V10
