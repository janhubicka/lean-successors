import SuccessorTree.V10.LocalAgeNeutralShapeMap
import Mathlib.Tactic

/-!
# Every level of the admissible Kpt tree is inhabited

The neutral singleton type is allowed: every forbidden singleton is
non-neutral and every nontrivial forbidden structure is irreducible in a
binary relational language. This supplies a single explicit Kpt node at
EVERY free-level cut n.

Take the finite all-neutral L structure on n+2 vertices, and let
E(u,v) hold precisely for v=n+1 and u<n. Its unique positive E column
is downward closed and spaced. No L pair is linked; consequently the
third partial-structure axiom is vacuous. Every singleton is neutral
and there are no off-diagonal L edges, so every normalized forbidden
pattern is avoided. The last vertex has canonical free cut n.

This discharges the missing nonemptiness condition for showing that the
neutral ShapeMap skips ONLY the inserted positive level ell.
-/

namespace SuccessorTree.V10

/-- An entirely neutral finite L-reduct with the real finite carrier. -/
def pureNeutralL (db du dd size : Nat) : AgeTestModel db du dd where
  carrier := {v | v < size}
  binary := fun _ _ _ => false
  unary := fun _ _ => false
  diagonal := fun _ _ => false

/-- All E-incidences into the final type vertex, exactly through cut n. -/
def pureNeutralE (n u v : Nat) : Bool :=
  decide (v = n + 1 ∧ u < n)

theorem pureNeutralE_inside
    (n u v : Nat) (he : pureNeutralE n u v = true) :
    u < n + 2 ∧ v < n + 2 := by
  have hh : v = n + 1 ∧ u < n := by
    simpa [pureNeutralE] using he
  omega

theorem pureNeutralE_spaced (n : Nat) : SpacedE (pureNeutralE n) := by
  intro u v he
  have hh : v = n + 1 ∧ u < n := by
    simpa [pureNeutralE] using he
  omega

theorem pureNeutralE_downward (n : Nat) : DownwardE (pureNeutralE n) := by
  intro u v he w hw
  have hh : v = n + 1 ∧ u < n := by
    simpa [pureNeutralE] using he
  exact show pureNeutralE n w v = true by
    simp [pureNeutralE, hh.1, lt_trans hw hh.2]

/-- The all-neutral structure is an honest L+ partial structure. -/
def pureNeutralPartial
    (db du dd n : Nat) : EnumeratedPartialStructure db du dd := by
  refine
    { size := n + 2
      L := pureNeutralL db du dd (n + 2)
      carrier_iff := ?_
      E := pureNeutralE n
      E_inside := pureNeutralE_inside n
      spaced := pureNeutralE_spaced n
      downward := pureNeutralE_downward n
      linked_E := ?_ }
  · intro v
    rfl
  · intro u v huv hu hv hlink
    obtain ⟨t, ht⟩ := hlink
    simp [pureNeutralL] at ht

/-- The free E-cut of the last vertex is exactly the chosen n. -/
theorem pureNeutralPartial_freeLevel
    (db du dd n : Nat) :
    (pureNeutralPartial db du dd n).freeLevel (n + 1) = n := by
  let A := pureNeutralPartial db du dd n
  have hCut : IsFreeCut A.E (n + 1) n := by
    change IsFreeCut (pureNeutralE n) (n + 1) n
    constructor
    · intro u hu
      simp [pureNeutralE, hu]
    · simp [pureNeutralE]
  exact freeCut_unique A.E (n + 1) (A.freeLevel (n + 1)) n
    (canonicalFreeLevel_isFreeCut A.E A.spaced A.downward (n + 1))
    hCut

/-- No normalized forbidden singleton or irreducible larger forbidden
structure admits an induced ordered copy in an all-neutral L model. -/
theorem pureNeutralL_avoids
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (size : Nat) :
    ∀ bad, bad ∈ family →
      bad.Avoids (pureNeutralL db du dd size) := by
  intro bad hbad
  cases bad with
  | singleton F hNonNeutral =>
      rintro ⟨f, hCopy⟩
      rcases hNonNeutral with ⟨t,ht⟩ | ⟨t,ht⟩
      · have heq := hCopy.2.2.2.1 0 t
        change false = F.unary 0 t at heq
        rw [ht] at heq
        contradiction
      · have heq := hCopy.2.2.2.2 0 t
        change false = F.diagonal 0 t at heq
        rw [ht] at heq
        contradiction
  | nontrivial r F hr hIrred =>
      rintro ⟨f, hCopy⟩
      have hne : (0 : Fin r) ≠ 1 := by
        intro h
        have hv := congrArg Fin.val h
        norm_num at hv
      obtain ⟨t,ht⟩ := hIrred 0 1 hne
      have hf := hCopy.2.2.1 0 1 hne t
      have hb := hCopy.2.2.1 1 0 hne.symm t
      change false = F.binary 0 1 t at hf
      change false = F.binary 1 0 t at hb
      rcases ht with hh | hh
      · rw [hh] at hf
        contradiction
      · rw [hh] at hb
        contradiction

/-- Every natural level is inhabited by a genuinely admissible type in
the normalized forbidden-free Kpt forest, without an M3 assumption. -/
theorem admissibleKptLevel_nonempty
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) :
    ∃ a : AdmissibleKptNode family, a.1.1 = n := by
  let A := pureNeutralPartial db du dd n
  have hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L :=
    pureNeutralL_avoids family (n + 2)
  have hv : n + 1 < A.size := by
    change n + 1 < n + 2
    omega
  let a : AdmissibleKptNode family :=
    ⟨A.rawTypeAtFree (n + 1), ⟨A, n+1, hv, hAvoid, rfl⟩⟩
  refine ⟨a, ?_⟩
  change A.freeLevel (n + 1) = n
  exact pureNeutralPartial_freeLevel db du dd n

/-- Every target level OTHER THAN ell appears in the neutral ShapeMap's
range. The level ell is missed. This is the exact SkipsOnly statement
needed in the manuscript's one-level boring-extension formulation, but
the map here is only the all-neutral (not prescribed) version. -/
theorem neutralKptShapeMap_skipsOnly
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell) :
    (neutralKptShapeMap family ell hellPos).SkipsOnly ell := by
  unfold SuccessorTree.ShapeMap.SkipsOnly
  ext q
  constructor
  · rintro ⟨a,ha⟩
    intro heq
    subst q
    exact neutralKptShapeMap_skips family ell hellPos ⟨a,ha⟩
  · intro hq
    by_cases hlt : q < ell
    · obtain ⟨a,ha⟩ := admissibleKptLevel_nonempty family q
      refine ⟨a, ?_⟩
      change (neutralKptSkip family ell hellPos a).1.1 = q
      rw [neutralKptSkip_level, ha]
      simp [Nat.not_le.mpr hlt]
    · have hgt : ell < q := by omega
      obtain ⟨a,ha⟩ := admissibleKptLevel_nonempty family (q-1)
      refine ⟨a, ?_⟩
      change (neutralKptSkip family ell hellPos a).1.1 = q
      rw [neutralKptSkip_level, ha]
      have hge : ell ≤ q-1 := by omega
      simp [hge]
      omega

end SuccessorTree.V10
