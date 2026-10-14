import SuccessorTree.V10.M2ImageLowerSocle
import SuccessorTree.V10.M2CopyFromCompleteImageTypes
import Mathlib.Tactic

/-!
# The initial comparison can be recovered from one complete upper parameter

A complete image ordinary type at an actual upper coordinate includes the
whole common lower socle. Thus the final contradiction does not need an
additional premise comparing the initial socle, provided there is at least
one upper selected coordinate. The zero-upper case is separately ruled out
by the admissibility of the prescribed lower image type.
-/
namespace SuccessorTree.V10

/-- The full image type of ONE selected upper vertex identifies the entire
lower socle (through the gap) with the target witness. Its carrier condition
is exactly that every lower target position is actually present. -/
theorem sameInitialL_of_complete_upper_type
    {N db du dd : Nat}
    (Q : PartialTypeWithE N db du dd)
    (W : AgeTestModel db du dd) (m j w : Nat)
    (hj : j < N) (hq : m+1 ≤ N)
    (hWCarrier : ∀ k, k ≤ m → k ∈ W.carrier)
    (hType : (Q.ordinaryType j hj (m+1) hq).lReduct =
      RelationalPrefixType.ofAgeModel W (m+1) w) :
    SameInitialL Q.ageModel W m := by
  obtain ⟨hB,hU,hD⟩ :=
    image_ordinary_type_all_lower_atoms Q j hj hq W w hType
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k hk
    change (k ≤ N ↔ k ∈ W.carrier)
    constructor
    · intro _hk
      exact hWCarrier k hk
    · intro _hk
      omega
  · intro k l hk hl t
    exact hB k l (by omega) (by omega) t
  · intro k hk t
    exact hU k (by omega) t
  · intro k hk t
    exact hD k (by omega) t

/-- A single upper forbidden-copy vertex discharges the common initial-socle
premise of the exact mixed forbidden-copy assembly. -/
theorem m2ForbiddenCopy_from_upper_records
    {N r db du dd : Nat}
    (Q : PartialTypeWithE N db du dd)
    (W : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m : Nat) (e : Fin r → Nat)
    (hLambda : StrictMono lambda) (hGap : m < lambda n)
    (hCarrier : ∀ k, k ≤ m → k ∈ W.carrier)
    (hExists : ∃ a : Fin r, m < e a)
    (hUpper : ∀ (a : Fin r) (_ha : m < e a),
      ∃ (hj : lambda (NonedgePadding.address n (n+a.val)) < N)
        (hq : m+1 ≤ N),
        (Q.ordinaryType (lambda (NonedgePadding.address n (n+a.val)))
          hj (m+1) hq).lReduct =
            RelationalPrefixType.ofAgeModel W (m+1) (e a))
    (hHighHigh : ∀ (a b : Fin r), m < e a → m < e b →
      ∀ t : Fin db,
        Q.ageModel.binary
          (lambda (NonedgePadding.address n (n+a.val)))
          (lambda (NonedgePadding.address n (n+b.val))) t =
            W.binary (e a) (e b) t)
    (P : ForbiddenAtomicPattern r db du dd)
    (hCopy : W.Realizes P e) :
    Q.ageModel.Realizes P (m2ForbiddenCopyImage lambda n m r e) := by
  obtain ⟨a, ha⟩ := hExists
  obtain ⟨hj,hq,hType⟩ := hUpper a ha
  have hInitial := sameInitialL_of_complete_upper_type Q W m
    (lambda (NonedgePadding.address n (n+a.val))) (e a)
    hj hq hCarrier hType
  exact m2ForbiddenCopy_from_complete_upper_types
    Q W lambda n m e hLambda hGap hInitial hUpper hHighHigh P hCopy

end SuccessorTree.V10
