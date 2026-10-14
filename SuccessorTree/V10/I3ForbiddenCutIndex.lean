import SuccessorTree.V10.I3AgeFailure
import Mathlib.Tactic

/-!
# The lower/upper cut of an actual I3 ordered forbidden copy

The manuscript uses a nonempty PROPER initial segment of an ordered
forbidden copy lying at or below the tested coordinate ell. It should
not be selected by an arbitrary enumeration or introduced as an
extra assumption: once the actual copy contains ell and also has
an upper vertex, strict monotonicity determines this cut uniquely.

This elementary lemma supplies the exact r, its final index r-1,
and the low/high position inequalities used by Lemma 6.53.
It is independent of axiomatic weakening, E, the H generation
construction and the future general-language paper.
-/

namespace SuccessorTree.V10

/-- An ordered copy meeting ell and extending above ell has an
unambiguously determined nonempty proper lower initial segment.
The last lower vertex is exactly ell; every later copy vertex
lies strictly above ell. -/
theorem ordered_I3_copy_has_exact_lower_cut
    {t : Nat}
    (e : Fin t → Nat) (hMono : StrictMono e)
    (ell : Nat)
    (hAt : ∃ a : Fin t, e a = ell)
    (hUpper : ∃ b : Fin t, ell < e b) :
    ∃ (r : Nat) (_hr : 0 < r) (_hrt : r < t),
      e (⟨r-1, by omega⟩ : Fin t) = ell ∧
      (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
      (∀ a : Fin t, r ≤ a.val ↔ ell < e a) := by
  obtain ⟨a,ha⟩ := hAt
  obtain ⟨b,hb⟩ := hUpper
  have hab : a < b := by
    by_contra h
    have hba : b ≤ a := le_of_not_gt h
    have hMon := hMono.monotone hba
    omega
  let r := a.val+1
  have hr0 : 0 < r := by dsimp [r]; omega
  have hrt : r < t := by
    have hab' := Fin.lt_def.mp hab
    have hbt := b.isLt
    dsimp [r]
    omega
  have hLast : e (⟨r-1, by omega⟩ : Fin t) = ell := by
    have heq : (⟨r-1, by omega⟩ : Fin t) = a := Fin.ext (by
      simp [r])
    rw [heq]
    exact ha
  have hLow : ∀ c : Fin t, c.val < r ↔ e c ≤ ell := by
    intro c
    constructor
    · intro hc
      have hca : c ≤ a := Fin.le_def.mpr (by
        dsimp [r] at hc
        omega)
      have hce := hMono.monotone hca
      omega
    · intro he
      by_contra hc
      have hac : a < c := Fin.lt_def.mpr (by
        dsimp [r] at hc
        omega)
      have hec := hMono hac
      omega
  refine ⟨r,hr0,hrt,hLast,hLow,?_⟩
  intro c
  constructor
  · intro hc
    by_contra h
    have hLe : e c ≤ ell := Nat.le_of_not_gt h
    have hcLow := (hLow c).2 hLe
    omega
  · intro he
    by_contra hc
    have hcLow : c.val < r := Nat.lt_of_not_ge hc
    have hLe := (hLow c).1 hcLow
    omega

/-- For a genuine finite I3 age witness, a forbidden copy meeting
the tested coordinate and having an upper vertex has exactly the
lower-prefix decomposition used in the signature and generation
arguments. No signature assignment is needed to obtain its cut. -/
theorem i3_forbidden_age_copy_lower_cut
    {db du dd t : Nat}
    (W : AgeTestModel db du dd)
    (P : ForbiddenAtomicPattern t db du dd)
    (e : Fin t → Nat)
    (hCopy : W.Realizes P e)
    (ell : Nat)
    (hAt : ∃ a : Fin t, e a = ell)
    (hUpper : ∃ b : Fin t, ell < e b) :
    ∃ (r : Nat) (_hr : 0 < r) (_hrt : r < t),
      e (⟨r-1, by omega⟩ : Fin t) = ell ∧
      (∀ a : Fin t, a.val < r ↔ e a ≤ ell) ∧
      (∀ a : Fin t, r ≤ a.val ↔ ell < e a) :=
  ordered_I3_copy_has_exact_lower_cut e hCopy.1 ell hAt hUpper

end SuccessorTree.V10
