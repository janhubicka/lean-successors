import SuccessorTree.V10.HActualMeet

/-!
# The exact finite numerical H+ partial structure

All ordered binary atoms and the downward-generated E relation are now in
one actual finite EnumeratedPartialStructure. Unary and diagonal atoms are
copied from the uniquely represented real vertex, with a neutral singleton
at fake vertices. Only E's target is clipped to the finite initial segment:
spacing then puts its source in the carrier as well.

The three E axioms are proved from the exact generators. The NumericHOn
interface is satisfied by this constructor, not supplied by the caller.
Forbidden-age preservation is a separate statement about its L-reduct.
-/

namespace SuccessorTree.V10

/-- An incident numerical L-pair in increasing order recovers exactly
an allowed earlier/later real generator, irrespective of orientation. -/
theorem hNumericBinary_linked_generators
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k x y : Nat)
    (hxy : x < y)
    (hLink : ∃ a : Fin db,
      hNumericBinary B k x y a = true ∨ hNumericBinary B k y x a = true) :
    ∃ i j q m : Nat,
      i < j ∧ q ≤ k ∧ m ≤ k ∧
      (q < m ∨ (q = m ∧ m = k)) ∧
      x = hPosition k i q ∧ y = hPosition k j m := by
  obtain ⟨a, ha | ha⟩ := hLink
  · obtain ⟨i, j, q, m, hij, hq, hm, hgate, hdir⟩ :=
      (hNumericBinary_true_iff B k x y a).1 ha
    have hpos := hPosition_lt_of_block_lt k i j q m hq hij
    rcases hdir with ⟨hx, hy, _⟩ | ⟨hx, hy, _⟩
    · exact ⟨i, j, q, m, hij, hq, hm, hgate, hx, hy⟩
    · omega
  · obtain ⟨i, j, q, m, hij, hq, hm, hgate, hdir⟩ :=
      (hNumericBinary_true_iff B k y x a).1 ha
    have hpos := hPosition_lt_of_block_lt k i j q m hq hij
    rcases hdir with ⟨hy, hx, _⟩ | ⟨hy, hx, _⟩
    · omega
    · exact ⟨i, j, q, m, hij, hq, hm, hgate, hx, hy⟩

/-- E3 for the actual ordered numerical binary relation. -/
theorem hNumericBinary_linked_E
    {db : Nat} (B : Nat → Nat → Fin db → Bool) (k x y : Nat)
    (hxy : x < y)
    (hLink : ∃ a : Fin db,
      hNumericBinary B k x y a = true ∨ hNumericBinary B k y x a = true) :
    exactHEBool k x y = true := by
  obtain ⟨i, j, q, m, hij, hq, hm, hgate, hx, hy⟩ :=
    hNumericBinary_linked_generators B k x y hxy hLink
  apply (exactHEBool_true_iff k x y).2
  refine ⟨j, m, hm, hy, ?_⟩
  rw [hx]
  exact generatedE_of_allowedPair k i j q m hij hq hgate

/-- Copy the base singleton at every real address; use the neutral
singleton if there is no real representation. Uniqueness is proved below. -/
noncomputable def hNumericSingleton {d : Nat}
    (U : Nat → Fin d → Bool) (k x : Nat) : Fin d → Bool := by
  classical
  exact if h : ∃ i g : Nat, g ≤ k ∧ x = hPosition k i g then
    U (Classical.choose h) else fun _ => false

@[simp] theorem hNumericSingleton_real
    {d : Nat} (U : Nat → Fin d → Bool) (k i g : Nat) (hg : g ≤ k) :
    hNumericSingleton U k (hPosition k i g) = U i := by
  classical
  have h : ∃ j m : Nat, m ≤ k ∧ hPosition k i g = hPosition k j m :=
    ⟨i, g, hg, rfl⟩
  have hChosen := Classical.choose_spec (Classical.choose_spec h)
  have hi := (hPosition_injective_bounded k i g
    (Classical.choose h) (Classical.choose (Classical.choose_spec h))
    hg hChosen.1 hChosen.2).1
  simp only [hNumericSingleton, dite_eq_left h]
  rw [← hi]

/-- Fake singletons contain no unary or diagonal facts. -/
theorem hNumericSingleton_no_real
    {d : Nat} (U : Nat → Fin d → Bool) (k x : Nat)
    (h : ¬ ∃ i g : Nat, g ≤ k ∧ x = hPosition k i g) :
    hNumericSingleton U k x = fun _ => false := by
  classical
  simp [hNumericSingleton, h]

@[simp] theorem hNumericSingleton_odd
    {d : Nat} (U : Nat → Fin d → Bool) (k a : Nat) :
    hNumericSingleton U k (2 * a + 1) = fun _ => false := by
  apply hNumericSingleton_no_real
  rintro ⟨i, g, _, h⟩
  obtain ⟨t, ht⟩ := hPosition_even k i g
  omega

/-- The exact finite L-reduct, with singleton data copied from K. -/
noncomputable def finiteNumericHL {db du dd : Nat}
    (K : AgeTestModel db du dd) (k N : Nat) : AgeTestModel db du dd :=
  { carrier := {x | x < N}
    binary := hNumericBinary K.binary k
    unary := hNumericSingleton K.unary k
    diagonal := hNumericSingleton K.diagonal k }

/-- Restrict generated E to targets in the finite initial segment. -/
noncomputable def finiteNumericHE (k N x y : Nat) : Bool :=
  if y < N then exactHEBool k x y else false

theorem finiteNumericHE_true_iff (k N x y : Nat) :
    finiteNumericHE k N x y = true ↔ y < N ∧ exactHEBool k x y = true := by
  by_cases hy : y < N <;> simp [finiteNumericHE, hy]

/-- A literal finite partial structure: all E axioms are consequences
of the generated relation and exact binary interpretation. -/
noncomputable def finiteNumericH {db du dd : Nat}
    (K : AgeTestModel db du dd) (k N : Nat) : EnumeratedPartialStructure db du dd where
  size := N
  L := finiteNumericHL K k N
  carrier_iff := by intro v; rfl
  E := finiteNumericHE k N
  E_inside := by
    intro x y h
    obtain ⟨hy, hE⟩ := (finiteNumericHE_true_iff k N x y).1 h
    have hs := exactHEBool_spaced k x y hE
    exact ⟨by omega, hy⟩
  spaced := by
    intro x y h
    exact exactHEBool_spaced k x y ((finiteNumericHE_true_iff k N x y).1 h).2
  downward := by
    intro x y h z hz
    obtain ⟨hy, hE⟩ := (finiteNumericHE_true_iff k N x y).1 h
    exact (finiteNumericHE_true_iff k N z y).2
      ⟨hy, exactHEBool_downward k x y hE z hz⟩
  linked_E := by
    intro x y hxy _hx hy hLink
    exact (finiteNumericHE_true_iff k N x y).2
      ⟨hy, hNumericBinary_linked_E K.binary k x y hxy hLink⟩

/-- The hypothesis used by the actual-meet theorem is now discharged
for the explicit constructor; no caller-supplied trace identification. -/
theorem finiteNumericH_matches
    {db du dd : Nat} (K : AgeTestModel db du dd) (k N : Nat) :
    NumericHOn (finiteNumericH K k N) K.binary k := by
  constructor
  · intro x y _hx _hy
    rfl
  · intro x y _hx hy
    change finiteNumericHE k N x y = exactHEBool k x y
    change y < N at hy
    simp [finiteNumericHE, hy]

/-- The original of a carrier vertex, with admissibility obtained
from the forbidden-free ambient structure rather than postulated. -/
noncomputable def finiteNumericHOriginal
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids (finiteNumericHL K k N))
    (v : Nat) (hv : v < N) : AdmissibleKptNode family :=
  ⟨(finiteNumericH K k N).rawTypeAtFree v,
    ⟨finiteNumericH K k N, v, hv, hAvoid, rfl⟩⟩

/-- The complete charged-meet conclusion for the CONSTRUCTED finite H+.
Only its forbidden-free age is still required by this local theorem. -/
theorem finiteNumericH_prefix_meet_charge
    {db du dd : Nat} (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat) (hk : 0 < k)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids (finiteNumericHL K k N))
    (v w : Nat) (hv : v < N) (hw : w < N)
    (s t : AdmissibleKptNode family)
    (hs : s ≤ finiteNumericHOriginal family K k N hAvoid v hv)
    (ht : t ≤ finiteNumericHOriginal family K k N hAvoid w hw)
    (hCommon : ∃ c : AdmissibleKptNode family, c ≤ s ∧ c ≤ t)
    (hStrictS : LevelTree.meet s t ≠ s)
    (hStrictT : LevelTree.meet s t ≠ t)
    (p r : Nat) (hr : 0 < r) (hrk : r ≤ k)
    (hMeet : LevelTree.lev (LevelTree.meet s t) = hPosition k p r) :
    NumericHMeetCharge K.binary k v w p r :=
  NumericHOn.prefix_meet_charge family (finiteNumericH K k N) K.binary k hk
    (finiteNumericH_matches K k N) v w hv hw
    ⟨finiteNumericH K k N, v, hv, hAvoid, rfl⟩
    ⟨finiteNumericH K k N, w, hw, hAvoid, rfl⟩
    s t hs ht hCommon hStrictS hStrictT p r hr hrk hMeet

end SuccessorTree.V10
