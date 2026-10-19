import SuccessorTree.V10.FiniteTypeProfileContinuation
import SuccessorTree.V10.FiniteTypeProfileRecovery

/-!
# The intrinsic continuation condition is equality of labelled ages

The definition supplies a finite allowed continuation with the transported
labels. Complete labels and the upper structure determine every induced
atom, so any continuation with those data is allowed. Conversely, the
finite successor laws recover the source on the retained coordinates.
This establishes the two-sided formulation without a global extension.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

@[simp] theorem RelationalPrefixType.reindexOrdinary_id {n : Nat}
    (Q : RelationalPrefixType n db du dd) : Q.reindexOrdinary id = Q := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    cases x <;> cases y <;> rfl
  · intro x t
    cases x <;> rfl
  · intro x t
    cases x <;> rfl

/-- An empty upper carrier leaves an allowed initial segment of the base. -/
theorem ProfileContinuation.avoids_of_no_upper
    {A : FiniteTypeBase family} {i : Fin (A.size+1)}
    {r : Nat} {P : Set (Fin r)} {labels : Fin r → AdmissibleKptNode family}
    {W : AgeTestModel db du dd}
    (hW : ProfileContinuation A i r P labels W) (hEmpty : ¬ P.Nonempty) :
    ∀ bad, bad ∈ family → bad.Avoids W := by
  have hLow (x : Nat) (hx : x ∈ W.carrier) : x < i.val := by
    rcases (hW.carrier x).1 hx with hx | ⟨a,ha,rfl⟩
    · exact hx
    · exact (hEmpty ⟨a,ha⟩).elim
  let H : W.InducedEmbeddingOnCarrier A.str.L := {
    toFun := id
    order := fun _ _ _ _ hxy => hxy
    inside := by
      intro x hx
      exact (A.str.carrier_iff x).2 (by
        change x < A.size
        have hxLow := hLow x hx
        have hi := i.isLt
        omega)
    binary := by
      intro x y hx hy hxy t
      exact (hW.binary_socle ⟨x,hLow x hx⟩ ⟨y,hLow y hy⟩ t).symm
    unary := by
      intro x hx t
      exact (hW.unary_socle ⟨x,hLow x hx⟩ t).symm
    diagonal := by
      intro x hx t
      exact (hW.diagonal_socle ⟨x,hLow x hx⟩ t).symm }
  exact H.preserves_avoidance family A.avoids

private theorem reindexOrdinary_eq_of_sigma
    {n m N M : Nat}
    (Q : RelationalPrefixType n db du dd) (R : RelationalPrefixType m db du dd)
    (U : RelationalPrefixType N db du dd) (V : RelationalPrefixType M db du dd)
    (hQ : (⟨n,Q⟩ : RawRelationalTypeNode db du dd) = ⟨N,U⟩)
    (hR : (⟨m,R⟩ : RawRelationalTypeNode db du dd) = ⟨M,V⟩)
    (rho : Fin n → Fin m) (alpha : Fin N → Fin M)
    (hIndex : ∀ x : Fin n, ∀ y : Fin N, x.val = y.val →
      (rho x).val = (alpha y).val)
    (hRecover : V.reindexOrdinary alpha = U) :
    Q = R.reindexOrdinary rho := by
  have hn : n = N := congrArg Sigma.fst hQ
  have hm : m = M := congrArg Sigma.fst hR
  subst N
  subst M
  have hQ' : Q = U := eq_of_heq (Sigma.mk.inj_iff.mp hQ).2
  have hR' : R = V := eq_of_heq (Sigma.mk.inj_iff.mp hR).2
  have hIndex' : rho = alpha := funext (fun x => Fin.ext (hIndex x x rfl))
  rw [hQ',hR',hIndex']
  exact hRecover.symm

namespace CoherentTypeProfileMap

variable {A B : FiniteTypeBase family}

/-- The retained ordinary coordinates below a cut, independent of the
choice of a type on that front. -/
def frontIndex (h : CoherentTypeProfileMap A B) (i : Fin (A.size+1))
    (x : Fin i.val) : Fin (h.cutMap i).val :=
  ⟨h.levelMap x.val ((Nat.le_of_lt x.isLt).trans (Nat.le_of_lt_succ i.isLt)), by
    exact h.cut_strictMono x.isLt⟩

theorem frontIndex_strictMono (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size+1)) : StrictMono (h.frontIndex i) := by
  intro x y hxy
  have hx : x.val ≤ A.size :=
    (Nat.le_of_lt x.isLt).trans (Nat.le_of_lt_succ i.isLt)
  have hy : y.val ≤ A.size :=
    (Nat.le_of_lt y.isLt).trans (Nat.le_of_lt_succ i.isLt)
  change h.levelMap x.val hx < h.levelMap y.val hy
  exact h.levelMap_strictMono hx hy hxy

/-- The complete source continuation type is recovered by the finite
intrinsic successor laws, without any age or extendability premise. -/
theorem recovers_continuation_type (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size+1)) (u : TypeProfile A)
    (W V : AgeTestModel db du dd) (w v : Nat)
    (hW : (⟨i.val,RelationalPrefixType.ofAgeModel W i.val w⟩ :
      RawRelationalTypeNode db du dd) = u.1.relationalNode)
    (hV : (⟨(h.cutMap i).val,
      RelationalPrefixType.ofAgeModel V (h.cutMap i).val v⟩ :
      RawRelationalTypeNode db du dd) = (h u).relationalNode) :
    RelationalPrefixType.ofAgeModel W i.val w =
      (RelationalPrefixType.ofAgeModel V (h.cutMap i).val v).reindexOrdinary
        (h.frontIndex i) := by
  apply reindexOrdinary_eq_of_sigma _ _ u.1.1.2.lReduct (h u).1.2.lReduct
    hW hV (h.frontIndex i) (h.retainedIndex u)
  · intro x y hxy
    change h.levelMap x.val
        ((Nat.le_of_lt x.isLt).trans (Nat.le_of_lt_succ i.isLt)) =
      h.levelMap y.val ((Nat.le_of_lt y.isLt).trans u.level_le_size)
    unfold levelMap
    apply congrArg Fin.val
    apply congrArg h.cutMap
    exact Fin.ext hxy
  · exact congrArg (fun Q : PartialTypeWithE u.level db du dd => Q.lReduct)
      (h.recovers_complete_record u)

/-- Reflection of forbidden avoidance follows already from the finite
coherent part of a type-respecting map. -/
theorem reflects_continuation_age (h : CoherentTypeProfileMap A B)
    (i : Fin (A.size+1)) (r : Nat) (P : Set (Fin r))
    (labels : Fin r → TypeProfile A) (W V : AgeTestModel db du dd)
    (hW : ProfileContinuation A i r P (fun a => (labels a).1) W)
    (hV : ProfileContinuation B (h.cutMap i) r P (fun a => h (labels a)) V)
    (hUpper : SameUpperL W V i.val (h.cutMap i).val r P)
    (hAvoidV : ∀ bad, bad ∈ family → bad.Avoids V) :
    ∀ bad, bad ∈ family → bad.Avoids W := by
  classical
  by_cases hP : P.Nonempty
  · obtain ⟨H⟩ := continuation_induced_of_types W V P (h.frontIndex i)
      (h.frontIndex_strictMono i) hP hW.carrier hV.carrier (by
        intro a ha
        exact h.recovers_continuation_type i (labels a) W V _ _
          (hW.upper_types a ha) (hV.upper_types a ha)) hUpper.binary
    exact H.preserves_avoidance family hAvoidV
  · exact hW.avoids_of_no_upper hP

end CoherentTypeProfileMap

/-- The existential finite continuation condition is the manuscript's
equality of allowed labelled ages, including repeated labels. -/
theorem FiniteTypeProfileMap.age_iff
    {A B : FiniteTypeBase family} (h : FiniteTypeProfileMap A B)
    (i : Fin (A.size+1)) (r : Nat) (P : Set (Fin r))
    (labels : Fin r → TypeProfile A) (W V : AgeTestModel db du dd)
    (hW : ProfileContinuation A i r P (fun a => (labels a).1) W)
    (hV : ProfileContinuation B (h.toCoherentTypeProfileMap.cutMap i) r P
      (fun a => h (labels a)) V)
    (hUpper : SameUpperL W V i.val
      (h.toCoherentTypeProfileMap.cutMap i).val r P) :
    (∀ bad, bad ∈ family → bad.Avoids W) ↔
      (∀ bad, bad ∈ family → bad.Avoids V) := by
  classical
  let g := h.toCoherentTypeProfileMap
  constructor
  · intro hAvoidW
    by_cases hP : P.Nonempty
    · obtain ⟨V0,hV0,hUpper0,hAvoidV0⟩ := h.age i r P labels W hW hAvoidW
      have hSame : SameUpperL V V0 (g.cutMap i).val (g.cutMap i).val r P :=
        hUpper.symm.trans hUpper0
      obtain ⟨H⟩ := continuation_induced_of_types V V0 P id
        (by intro x y hxy; exact hxy) hP hV.carrier hV0.carrier (by
          intro a ha
          have hSigma := (hV.upper_types a ha).trans (hV0.upper_types a ha).symm
          have hType := eq_of_heq (Sigma.mk.inj_iff.mp hSigma).2
          simpa only [RelationalPrefixType.reindexOrdinary_id] using hType)
        hSame.binary
      exact H.preserves_avoidance family hAvoidV0
    · exact hV.avoids_of_no_upper hP
  · exact g.reflects_continuation_age i r P labels W V hW hV hUpper

end SuccessorTree.V10
