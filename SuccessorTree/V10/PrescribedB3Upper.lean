import SuccessorTree.V10.PrescribedUpperSelection
import SuccessorTree.V10.LocalAgeForbiddenTest
import Mathlib.Tactic

/-!
# The genuine shifted-upper age-test condition, without a placeholder

Lemma 6.51 applies its finite B3 no-age-change hypothesis to the inserted
L-structure. The upper-type premise must quantify over TARGET vertices x
strictly above ell, rather than over their original addresses u.

This module supplies exactly that address transport. The inverse
removeInserted takes x to u=x-1, the actual inserted binary relation
decodes to the chosen gated upper L-data, and the checked B1/B2 upper
selection theorem identifies the ENTIRE induced L-type through ell+1
with the prescribed f(T_u), whenever the inserted vertex and x are
linked by some directed relation.

No assumption identifying a type with f[S] remains in the conclusion:
it is a consequence of actual inserted atomic data and the B1/B2
compatibility of the selected ordinary lower column. The separate
common-socle age-test witness remains to be constructed.
-/

namespace SuccessorTree.V10

/-- The L-predicate of membership in the prescribed f[S] images, with
all auxiliary E data deliberately absent. -/
def PrescribedBoringData.PrescribedUpperLType
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (R : RelationalPrefixType (ell + 1) db du dd) : Prop :=
  ∃ T : PartialTypeWithE ell db du dd,
    T ∈ F.source ∧ R = (F.target T).lReduct

/-- Every linked UPPER vertex of the actual INSERTED L structure realizes
a complete prescribed f(T)-type through the newly inserted level. In
particular all negative binary facts and both directed orientations
agree, not merely the positive cross edges. -/
theorem PrescribedBoringData.insertL_linked_upper_is_prescribed
    {ell db du dd : Nat}
    (F : PrescribedBoringData ell db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (base : Nat)
    (P : LowerInsertedColumn ell db du dd)
    (hSelected :
      F.selectedLowerColumn (A.partialTypeAt ell base) = some P) :
    ∀ x : Nat, x < A.size + 1 → ell < x →
      (∃ t : Fin db,
        (insertL A ell (F.insertedLData A P)).binary ell x t = true ∨
        (insertL A ell (F.insertedLData A P)).binary x ell t = true) →
      F.PrescribedUpperLType
        (RelationalPrefixType.ofAgeModel
          (insertL A ell (F.insertedLData A P)) (ell+1) x) := by
  classical
  intro x hx hxell hLink
  let u := removeInserted ell x
  have hxne : x ≠ ell := by omega
  have hUx : insertAddress ell u = x :=
    insertAddress_removeInserted ell x hxne
  have hUge : ell ≤ u := by
    unfold u removeInserted
    have hn : ¬ x < ell := Nat.not_lt.mpr (Nat.le_of_lt hxell)
    simp [hn]
    omega
  have hUsize : u < A.size := by
    unfold u removeInserted
    have hn : ¬ x < ell := Nat.not_lt.mpr (Nat.le_of_lt hxell)
    simp [hn]
    omega
  have hForward : ∀ t : Fin db,
      (insertL A ell (F.insertedLData A P)).binary ell x t =
        (F.insertedLData A P).outgoing u t := by
    intro t
    simp [insertL, hxne, u]
  have hBackward : ∀ t : Fin db,
      (insertL A ell (F.insertedLData A P)).binary x ell t =
        (F.insertedLData A P).incoming u t := by
    intro t
    simp [insertL, hxne, u]
  have hDataLink : ∃ t : Fin db,
      (F.insertedLData A P).outgoing u t = true ∨
      (F.insertedLData A P).incoming u t = true := by
    obtain ⟨t, ht⟩ := hLink
    refine ⟨t, ?_⟩
    rcases ht with ht | ht
    · exact Or.inl ((hForward t).symm.trans ht)
    · exact Or.inr ((hBackward t).symm.trans ht)
  obtain ⟨T,hT,hType⟩ :=
    F.linked_upper_has_prescribed_L_type A base u P
      hUge hUsize hSelected hDataLink
  refine ⟨T,hT,?_⟩
  rw [← hUx]
  exact hType

end SuccessorTree.V10
