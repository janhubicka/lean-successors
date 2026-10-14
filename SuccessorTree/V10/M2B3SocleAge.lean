import SuccessorTree.V10.M2B3SelectedContradiction
import SuccessorTree.V10.PrescribedCompatibleB3
import Mathlib.Tactic

/-!
# M2: forbidden avoidance of the prescribed ordinary lower socle

The corrected finite L-age B3 test starts with the ordinary L-socle
of an admissible target type. This entire socle is already an induced
L-substructure of the admissible target's finite L model. In
particular, every normalized forbidden pattern (including non-neutral
singletons) is absent from that socle. The age argument can therefore
discard forbidden copies with no vertex above the omitted level,
without assuming an extra avoidance hypothesis.

This proof does not require any auxiliary E-structure on a finite
B3 age witness. No M2 or B3 axiom is used.
-/

namespace SuccessorTree.V10

/-- The prescribed ordinary socle, with its exact induced unary,
diagonal and directed binary records, embeds on its genuine carrier
into the finite L-model of its complete admissible parent type. -/
def prescribedOrdinarySocle_induced
    {m db du dd : Nat}
    (Q : PartialTypeWithE (m+1) db du dd) :
    (prescribedOrdinarySocle Q).InducedEmbeddingOnCarrier Q.ageModel where
  toFun := id
  order := by
    intro x y _ _ hxy
    exact hxy
  inside := by
    intro x hx
    change x ≤ m at hx
    change x ≤ m+1
    omega
  binary := by
    intro x y hx hy _hne t
    change x ≤ m at hx
    change y ≤ m at hy
    have hx' : x < m+1 := by omega
    have hy' : y < m+1 := by omega
    simp [PartialTypeWithE.ageModel, prescribedOrdinarySocle,
      typeAgeIndex, hx, hy, hx', hy']
  unary := by
    intro x hx t
    change x ≤ m at hx
    have hx' : x < m+1 := by omega
    simp [PartialTypeWithE.ageModel, prescribedOrdinarySocle,
      typeAgeIndex, hx, hx']
  diagonal := by
    intro x hx t
    change x ≤ m at hx
    have hx' : x < m+1 := by omega
    simp [PartialTypeWithE.ageModel, prescribedOrdinarySocle,
      typeAgeIndex, hx, hx']

/-- The initial ordinary L-socle of ANY admissible target type is
forbidden-free, including all normalized singleton obstructions. -/
theorem prescribedOrdinarySocle_avoids_of_admissible
    {m db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Q : PartialTypeWithE (m+1) db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨m+1,Q⟩ : RawPartialTypeNode db du dd)) :
    ∀ bad, bad ∈ family → bad.Avoids (prescribedOrdinarySocle Q) := by
  exact (prescribedOrdinarySocle_induced Q).preserves_avoidance
    family (PartialTypeWithE.ageModel_avoids family Q hAd)

/-- A finite witness matching the ordinary socle of an admissible
prescribed output cannot realize a forbidden nontrivial pattern solely
at or below the inserted coordinate. No upper-vertex selection is
needed for this case. -/
theorem m2B3_nontrivial_copy_has_upper
    {m r db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Q : PartialTypeWithE (m+1) db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨m+1,Q⟩ : RawPartialTypeNode db du dd))
    (W : AgeTestModel db du dd)
    (P : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : P.Irreducible)
    (hMember : NormalizedForbidden.nontrivial r P hr hIrred ∈ family)
    (e : Fin r → Nat)
    (hSame : SameInitialL W (prescribedOrdinarySocle Q) m)
    (hCopy : W.Realizes P e) :
    ∃ a : Fin r, m < e a := by
  have hAvoid := prescribedOrdinarySocle_avoids_of_admissible family Q hAd
  exact forbiddenCopy_has_upper_of_sameInitialL W
    (prescribedOrdinarySocle Q) m P e hSame
      (hAvoid (.nontrivial r P hr hIrred) hMember) hCopy

end SuccessorTree.V10
