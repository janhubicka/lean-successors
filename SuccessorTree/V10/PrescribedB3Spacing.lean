import SuccessorTree.V10.AdmissibleKptPrefix
import SuccessorTree.V10.PartialStructureE
import Mathlib.Tactic

/-!
# An E-spacing obstruction to the printed B3 no-age-change premise

The manuscript's Lemma 6.51 currently quantifies over initially
enumerated partial structures A for which every upper vertex i>=ell+1
has the FULL level-(ell+1) partial type of one prescribed f(S).

There is a fundamental boundary obstruction. At the first upper index
i=ell+1, the spacing axiom prohibits E(ell,ell+1). But EVERY admissible
Kpt node at level ell+1 has E(ell,t), since the type vertex has free
level exactly ell+1.

Therefore NO nonempty upper tail of an initially enumerated partial
structure can consist entirely of prescribed admissible level-(ell+1)
types. The printed B3 antecedent, when interpreted in this exact
initial-ordinal model, excludes ALL structures with any upper vertex.

This does not refute the stronger finite COMMON-SOCLE L-age test used by
the repaired formalization; it shows why the former cannot simply be
asserted to imply that test. A repaired manuscript formulation needs
to allow sparse/weak upper witnesses or a suitable reindexing that does
not impose the forbidden E-edge on the first upper ordinal coordinate.
-/

namespace SuccessorTree.V10

/-- The E spacing axiom forbids consecutive E-pairs in every genuine
enumerated partial structure, independently of its language or age. -/
theorem adjacent_E_false
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) :
    A.E ell (ell+1) = false := by
  cases h : A.E ell (ell+1) with
  | false => rfl
  | true =>
      have hs := A.spaced ell (ell+1) h
      omega

/-- The final ordinary socle coordinate is E-linked to the distinguished
type vertex in EVERY admissible Kpt node at level ell+1. This follows
from an actual forbidden-free witness and the definition of free level,
not from an extra axiom on partial-type records. -/
theorem admissible_level_succ_has_last_E
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat)
    (Q : PartialTypeWithE (ell+1) db du dd)
    (hAd : IsAdmissibleRawType family
      (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd)) :
    Q.eRelation (some (Fin.last ell)) none = true := by
  obtain ⟨W,w,hw,hAvoid,hRaw⟩ := hAd
  have hFree : W.freeLevel w = ell + 1 := by
    have h := congrArg Sigma.fst hRaw
    change ell + 1 = W.freeLevel w at h
    omega
  have hType : Q = W.partialTypeAt (ell+1) w := by
    have hh :
        (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
        (⟨ell+1,W.partialTypeAt (ell+1) w⟩ :
          RawPartialTypeNode db du dd) := by
      calc
        (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) =
            W.rawTypeAtFree w := hRaw
        _ = (⟨ell+1,W.partialTypeAt (ell+1) w⟩ :
              RawPartialTypeNode db du dd) := by
            change
              (⟨W.freeLevel w,
                W.partialTypeAt (W.freeLevel w) w⟩ :
                RawPartialTypeNode db du dd) =
              (⟨ell+1,W.partialTypeAt (ell+1) w⟩ :
                RawPartialTypeNode db du dd)
            rw [hFree]
    exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  rw [hType]
  exact W.partialTypeAt_fullESocle (ell+1) w
    (by omega) (Fin.last ell)

/-- The type of the first upper ordinal vertex ell+1 through ell+1
CANNOT itself be an admissible level-(ell+1) Kpt type. Its final E bit
would violate the spacing axiom at two consecutive positions. -/
theorem first_upper_type_not_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat) :
    ¬ IsAdmissibleRawType family
      (⟨ell+1,A.partialTypeAt (ell+1) (ell+1)⟩ :
        RawPartialTypeNode db du dd) := by
  intro hAd
  have he := admissible_level_succ_has_last_E
    family ell (A.partialTypeAt (ell+1) (ell+1)) hAd
  change A.E ell (ell+1) = true at he
  have hFalse := adjacent_E_false A ell
  exact Bool.false_ne_true (hFalse.symm.trans he)

/-- No finite initial-ordinal partial structure with even ONE upper
vertex can have every upper level-(ell+1) type in the image of a map
to admissible level-(ell+1) Kpt nodes.

This is the precise obstruction in the printed B3 antecedent.
It does NOT assume any forbidden structure occurs. -/
theorem prescribed_tail_forces_no_upper
    {db du dd : Nat} {α : Type}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (ell : Nat)
    (f : α → AdmissibleKptNode family)
    (S : Set α)
    (hAll : ∀ i, ell+1 ≤ i → i < A.size →
      ∃ s, s ∈ S ∧
        (f s).1 =
          (⟨ell+1,A.partialTypeAt (ell+1) i⟩ :
            RawPartialTypeNode db du dd)) :
    A.size ≤ ell+1 := by
  by_contra hNo
  have hFirst : ell+1 < A.size := by omega
  obtain ⟨s,hs,hEq⟩ := hAll (ell+1) (by omega) hFirst
  have hAd : IsAdmissibleRawType family
      (⟨ell+1,A.partialTypeAt (ell+1) (ell+1)⟩ :
        RawPartialTypeNode db du dd) := by
    rw [← hEq]
    exact (f s).2
  exact first_upper_type_not_admissible family A ell hAd

end SuccessorTree.V10
