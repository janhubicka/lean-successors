import SuccessorTree.V10.CanonicalRawSTree
import Mathlib.Tactic

/-!
# Realising the terminal Sigma letter by a three-vertex partial structure

A level-one partial type from the terminal pair (ell,t) is not
literally an initial-socle restriction of the original type:
the chosen old vertex ell must first be renumbered to 0.

We provide an explicit small partial structure with vertices
0,1,2: vertex 0 represents ell, vertex 1 is a neutral filler,
and vertex 2 represents the original distinguished type vertex v.
The only E-pair is 0 -> 2. Every L-atom on {0,2} is copied from
the original {ell,v}, and all L-relations incident with the filler
are absent. This makes the new type vertex have free level 1.

We prove all three partial-structure E axioms and literal equality
of the extracted complete level-one L+ type with the terminal
Sigma letter. The separate forbidden-age preservation proof will
turn this into membership in the *admissible* alphabet Sigma.
-/

namespace SuccessorTree.V10

/-- The two original vertices survive; 1 is a neutral filler. -/
def terminalLetterAddress (ell v x : Nat) : Option Nat :=
  if x = 0 then some ell else if x = 2 then some v else none

@[simp] theorem terminalLetterAddress_zero (ell v : Nat) :
    terminalLetterAddress ell v 0 = some ell := by
  simp [terminalLetterAddress]

@[simp] theorem terminalLetterAddress_two (ell v : Nat) :
    terminalLetterAddress ell v 2 = some v := by
  simp [terminalLetterAddress]

@[simp] theorem terminalLetterAddress_one (ell v : Nat) :
    terminalLetterAddress ell v 1 = none := by
  simp [terminalLetterAddress]

/-- Exact directed L tuple copying from the original pair. -/
def terminalLetterReplicaL
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell v : Nat) : AgeTestModel db du dd :=
  { carrier := {x | x < 3}
    binary := fun x y r =>
      match terminalLetterAddress ell v x, terminalLetterAddress ell v y with
      | some a, some b => A.L.binary a b r
      | _, _ => false
    unary := fun x r =>
      match terminalLetterAddress ell v x with
      | some a => A.L.unary a r
      | none => false
    diagonal := fun x r =>
      match terminalLetterAddress ell v x with
      | some a => A.L.diagonal a r
      | none => false }

/-- The filler has the exact neutral L singleton and no L cross
tuple in either directed orientation. -/
theorem terminalLetterReplicaL_filler
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell v x : Nat) :
    (∀ r : Fin db,
      (terminalLetterReplicaL A ell v).binary 1 x r = false ∧
      (terminalLetterReplicaL A ell v).binary x 1 r = false) ∧
    (∀ r : Fin du,
      (terminalLetterReplicaL A ell v).unary 1 r = false) ∧
    (∀ r : Fin dd,
      (terminalLetterReplicaL A ell v).diagonal 1 r = false) := by
  constructor
  · intro r
    constructor <;> simp [terminalLetterReplicaL]
  constructor
  · intro r
    simp [terminalLetterReplicaL]
  · intro r
    simp [terminalLetterReplicaL]

/-- The E-pair 0 -> 2 is the entire E relation of the terminal
letter replica. It includes the filler spacing coordinate 1. -/
def terminalLetterReplicaE (u w : Nat) : Bool :=
  decide (u = 0 ∧ w = 2)

@[simp] theorem terminalLetterReplicaE_02 :
    terminalLetterReplicaE 0 2 = true := by
  simp [terminalLetterReplicaE]

theorem terminalLetterReplicaE_spaced :
    SpacedE terminalLetterReplicaE := by
  intro u w he
  have hh : u = 0 ∧ w = 2 := by
    simpa [terminalLetterReplicaE] using he
  rcases hh with ⟨rfl,rfl⟩
  omega

theorem terminalLetterReplicaE_downward :
    DownwardE terminalLetterReplicaE := by
  intro u w he z hz
  have hh : u = 0 ∧ w = 2 := by
    simpa [terminalLetterReplicaE] using he
  omega

theorem terminalLetterReplicaE_inside (u w : Nat)
    (he : terminalLetterReplicaE u w = true) :
    u < 3 ∧ w < 3 := by
  have hh : u = 0 ∧ w = 2 := by
    simpa [terminalLetterReplicaE] using he
  omega

/-- The pair replica satisfies E3: the only possible non-neutral
binary L-pair of distinct vertices is (0,2), which is always
E-related. -/
def terminalLetterReplicaPartial
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell v : Nat) : EnumeratedPartialStructure db du dd := by
  refine
    { size := 3
      L := terminalLetterReplicaL A ell v
      carrier_iff := ?_
      E := terminalLetterReplicaE
      E_inside := terminalLetterReplicaE_inside
      spaced := terminalLetterReplicaE_spaced
      downward := terminalLetterReplicaE_downward
      linked_E := ?_ }
  · intro x
    rfl
  · intro u w huw hu hw hlink
    by_cases h0 : u = 0
    · by_cases h2 : w = 2
      · subst u
        subst w
        exact terminalLetterReplicaE_02
      · have h1 : w = 1 := by omega
        obtain ⟨r, hrel⟩ := hlink
        rcases hrel with hrel | hrel
        · exfalso
          simpa [h1, h0, terminalLetterReplicaL] using hrel
        · exfalso
          simpa [h1, h0, terminalLetterReplicaL] using hrel
    · have h1 : u = 1 := by omega
      obtain ⟨r, hrel⟩ := hlink
      rcases hrel with hrel | hrel
      · exfalso
        simpa [h1, terminalLetterReplicaL] using hrel
      · exfalso
        simpa [h1, terminalLetterReplicaL] using hrel

theorem terminalLetterReplica_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell v : Nat) :
    (terminalLetterReplicaPartial A ell v).freeLevel 2 = 1 := by
  have hCut : IsFreeCut terminalLetterReplicaE 2 1 := by
    constructor
    · intro u hu
      have hu0 : u = 0 := by omega
      subst u
      exact terminalLetterReplicaE_02
    · simp [terminalLetterReplicaE]
  exact freeCut_unique terminalLetterReplicaE 2
    ((terminalLetterReplicaPartial A ell v).freeLevel 2) 1
    (canonicalFreeLevel_isFreeCut terminalLetterReplicaE
      terminalLetterReplicaE_spaced
      terminalLetterReplicaE_downward 2) hCut

/-- The genuine level-one complete partial type in the small
replica equals the exact terminal letter of the original
one-level type. All directed L, unary, diagonal and E facts
are accounted for, including their negative values. -/
theorem terminalLetterReplica_type_eq
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (ell v : Nat) (hSocle : ell + 1 ≤ A.freeLevel v) :
    (terminalLetterReplicaPartial A ell v).partialTypeAt 1 2 =
      (A.partialTypeAt (ell + 1) v).terminalLetter := by
  have hlt : ell < v := by
    have hfree := A.freeLevel_le v
    omega
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y r
      cases x with
      | none =>
        cases y with
        | none => rfl
        | some y =>
          have hy : y = 0 := Fin.eq_zero y
          subst y
          rfl
      | some x =>
        have hx : x = 0 := Fin.eq_zero x
        subst x
        cases y with
        | none => rfl
        | some y =>
          have hy : y = 0 := Fin.eq_zero y
          subst y
          rfl
    · intro x r
      cases x with
      | none => rfl
      | some x =>
        have hx : x = 0 := Fin.eq_zero x
        subst x
        rfl
    · intro x r
      cases x with
      | none => rfl
      | some x =>
        have hx : x = 0 := Fin.eq_zero x
        subst x
        rfl
  · intro x y
    cases x with
    | none =>
      cases y with
      | none =>
        change terminalLetterReplicaE 2 2 = A.E v v
        have hv0 := A.partialTypeAt_no_typeE_loop 0 v
        change A.E v v = false at hv0
        simp [terminalLetterReplicaE, hv0]
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change terminalLetterReplicaE 2 0 = A.E v ell
        have hFalse : A.E v ell = false := by
          cases he : A.E v ell with
          | false => rfl
          | true =>
              have hg := A.spaced v ell he
              omega
        simp [terminalLetterReplicaE, hFalse]
    | some x =>
      have hx : x = 0 := Fin.eq_zero x
      subst x
      cases y with
      | none =>
        change terminalLetterReplicaE 0 2 = A.E ell v
        have he : A.E ell v = true :=
          (A.E_iff_freeLevel ell v).2 (by omega)
        simp [terminalLetterReplicaE, he]
      | some y =>
        have hy : y = 0 := Fin.eq_zero y
        subst y
        change terminalLetterReplicaE 0 0 = A.E ell ell
        have he := A.partialTypeAt_no_typeE_loop 0 ell
        change A.E ell ell = false at he
        simp [terminalLetterReplicaE, he]

end SuccessorTree.V10
