import SuccessorTree.V10.TerminalLetterReplica
import SuccessorTree.V10.PrefixReplicaAge
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Forbidden-free terminal Sigma letters

The three-vertex terminal-letter replica has the two original
vertices ell<v at positions 0<2 and a completely L-neutral
filler at 1. A nontrivial irreducible forbidden ordered copy
cannot use the filler and therefore projects as an induced copy
into the original ambient A. A forbidden non-neutral singleton
cannot use the filler either.

Thus, assuming the normalized forbidden family, the replica
remains in the admissible age and realizes the complete terminal
two-vertex L+ letter at free level 1. This bridges the raw-letter
STree to the manuscript's actual admissible Sigma alphabet.
-/

namespace SuccessorTree.V10

/-- Original index assigned to every non-filler vertex of the
three-vertex letter replica. -/
def terminalLetterProject (ell v x : Nat) : Nat :=
  if x = 0 then ell else v

theorem terminalLetterProject_address
    (ell v x : Nat) (hx : x < 3) (hn : x ≠ 1) :
    terminalLetterAddress ell v x =
      some (terminalLetterProject ell v x) := by
  have hCases : x = 0 ∨ x = 2 := by omega
  rcases hCases with rfl | rfl
  · simp [terminalLetterProject]
  · simp [terminalLetterProject]

theorem terminalLetterProject_strictMono_on
    (ell v x y : Nat) (hlt : ell < v)
    (hx : x < 3) (hy : y < 3)
    (hnx : x ≠ 1) (hny : y ≠ 1)
    (hxy : x < y) :
    terminalLetterProject ell v x <
      terminalLetterProject ell v y := by
  have hx0 : x = 0 := by omega
  have hy2 : y = 2 := by omega
  subst x
  subst y
  simpa [terminalLetterProject] using hlt

/-- A nontrivial irreducible forbidden copy in the letter
replica cannot contain its neutral filler. -/
theorem irreducible_terminalLetter_copy_avoids_filler
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : F.Irreducible)
    (ell v : Nat)
    (f : Fin r → Nat)
    (hCopy : (terminalLetterReplicaL A ell v).Realizes F f) :
    ∀ a : Fin r, f a ≠ 1 := by
  have hBinary := hCopy.2.2.1
  let zero : Fin r := ⟨0, by omega⟩
  let one : Fin r := ⟨1, hr⟩
  intro a hFa
  obtain ⟨b, hab⟩ : ∃ b : Fin r, a ≠ b := by
    by_cases ha : a = zero
    · refine ⟨one, ?_⟩
      intro h
      have hv := congrArg Fin.val (ha.symm.trans h)
      norm_num [zero, one] at hv
    · exact ⟨zero, ha⟩
  obtain ⟨t, hRel⟩ := hIrred a b hab
  have hNeutral :=
    (terminalLetterReplicaL_filler A ell v (f b)).1 t
  rcases hRel with hRel | hRel
  · have hPreserve := hBinary a b hab t
    rw [hFa, hNeutral.1, hRel] at hPreserve
    contradiction
  · have hPreserve := hBinary b a hab.symm t
    rw [hFa, hNeutral.2, hRel] at hPreserve
    contradiction

/-- A forbidden non-neutral singleton cannot use the neutral
filler of the terminal-letter replica. -/
theorem nonNeutral_terminalLetter_singleton_avoids_filler
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern 1 db du dd)
    (hNonNeutral : F.NonNeutralSingleton)
    (ell v : Nat)
    (f : Fin 1 → Nat)
    (hCopy : (terminalLetterReplicaL A ell v).Realizes F f) :
    ∀ a : Fin 1, f a ≠ 1 := by
  intro a
  have ha : a = 0 := Fin.eq_zero a
  subst a
  intro hf
  rcases hNonNeutral with ⟨r,hR⟩ | ⟨r,hR⟩
  · have hp := hCopy.2.2.2.1 0 r
    have hn := (terminalLetterReplicaL_filler A ell v (f 0)).2.1 r
    rw [hf,hn,hR] at hp
    contradiction
  · have hp := hCopy.2.2.2.2 0 r
    have hn := (terminalLetterReplicaL_filler A ell v (f 0)).2.2 r
    rw [hf,hn,hR] at hp
    contradiction

/-- Every ordered induced forbidden copy disjoint from the filler
projects to the original forbidden-free ambient structure. -/
theorem terminalLetterReplica_copy_projects
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (ell v : Nat) (hell : ell < A.size)
    (hv : v < A.size) (hlt : ell < v)
    (f : Fin r → Nat)
    (hCopy : (terminalLetterReplicaL A ell v).Realizes F f)
    (hNoFiller : ∀ a : Fin r, f a ≠ 1) :
    A.L.Realizes F
      (fun a => terminalLetterProject ell v (f a)) := by
  obtain ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩ := hCopy
  have hAddress (a : Fin r) :
      terminalLetterAddress ell v (f a) =
        some (terminalLetterProject ell v (f a)) :=
    terminalLetterProject_address ell v (f a)
      (hIn a) (hNoFiller a)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact terminalLetterProject_strictMono_on ell v (f a) (f b)
      hlt (hIn a) (hIn b) (hNoFiller a) (hNoFiller b)
      (hMono hab)
  · intro a
    apply (A.carrier_iff (terminalLetterProject ell v (f a))).2
    have hCase : f a = 0 ∨ f a = 2 := by
      have h := hIn a
      have hN := hNoFiller a
      omega
    rcases hCase with hCase | hCase
    · simp [terminalLetterProject, hCase, hell]
    · simp [terminalLetterProject, hCase, hv]
  · intro a b hab t
    calc
      A.L.binary
          (terminalLetterProject ell v (f a))
          (terminalLetterProject ell v (f b)) t =
        (terminalLetterReplicaL A ell v).binary (f a) (f b) t := by
          simp [terminalLetterReplicaL, hAddress a, hAddress b]
      _ = F.binary a b t := hBinary a b hab t
  · intro a t
    calc
      A.L.unary (terminalLetterProject ell v (f a)) t =
        (terminalLetterReplicaL A ell v).unary (f a) t := by
          simp [terminalLetterReplicaL, hAddress a]
      _ = F.unary a t := hUnary a t
  · intro a t
    calc
      A.L.diagonal (terminalLetterProject ell v (f a)) t =
        (terminalLetterReplicaL A ell v).diagonal (f a) t := by
          simp [terminalLetterReplicaL, hAddress a]
      _ = F.diagonal a t := hDiagonal a t

/-- Normalized forbidden-free ages are preserved by the three-vertex
letter replica, including both singleton and irreducible cases. -/
theorem NormalizedForbidden.terminalLetter_preserves_avoidance
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (ell v : Nat) (hell : ell < A.size)
    (hv : v < A.size) (hlt : ell < v)
    (hAvoid : bad.Avoids A.L) :
    bad.Avoids (terminalLetterReplicaL A ell v) := by
  cases bad with
  | singleton F hNonNeutral =>
    rintro ⟨f, hCopy⟩
    have hNoFiller :=
      nonNeutral_terminalLetter_singleton_avoids_filler
        A F hNonNeutral ell v f hCopy
    exact hAvoid ⟨_, terminalLetterReplica_copy_projects
      A F ell v hell hv hlt f hCopy hNoFiller⟩
  | nontrivial r F hr hIrred =>
    rintro ⟨f,hCopy⟩
    have hNoFiller :=
      irreducible_terminalLetter_copy_avoids_filler
        A F hr hIrred ell v f hCopy
    exact hAvoid ⟨_, terminalLetterReplica_copy_projects
      A F ell v hell hv hlt f hCopy hNoFiller⟩

/-- The terminal letter of ANY genuine admissible cover belongs
to the published admissible level-one alphabet Sigma.

The proof supplies an explicit forbidden-free partial-structure
witness. Thus it does not merely assume that a raw two-vertex
type is admissible. -/
theorem terminalLetter_is_admissible
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (v ell : Nat) (hv : v < A.size)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L)
    (hCut : ell + 1 ≤ A.freeLevel v) :
    IsAdmissibleRawType family
      (⟨1, (A.partialTypeAt (ell + 1) v).terminalLetter⟩ :
        RawPartialTypeNode db du dd) := by
  have hlt : ell < v := by
    have hb := A.freeLevel_le v
    omega
  have hell : ell < A.size := Nat.lt_trans hlt hv
  let B := terminalLetterReplicaPartial A ell v
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L := by
    intro bad hm
    exact bad.terminalLetter_preserves_avoidance
      A ell v hell hv hlt (hAvoid bad hm)
  have hRaw :
      (⟨1, (A.partialTypeAt (ell + 1) v).terminalLetter⟩ :
        RawPartialTypeNode db du dd) =
      B.rawTypeAtFree 2 := by
    change
      (⟨1, (A.partialTypeAt (ell + 1) v).terminalLetter⟩ :
        RawPartialTypeNode db du dd) =
      (⟨B.freeLevel 2, B.partialTypeAt (B.freeLevel 2) 2⟩ :
        RawPartialTypeNode db du dd)
    have hFree : B.freeLevel 2 = 1 :=
      terminalLetterReplica_freeLevel A ell v
    rw [hFree]
    exact congrArg (Sigma.mk 1)
      (terminalLetterReplica_type_eq A ell v hCut).symm
  exact ⟨B,2,(by decide),hAvoidB,hRaw⟩

end SuccessorTree.V10
