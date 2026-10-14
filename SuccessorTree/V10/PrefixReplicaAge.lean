import SuccessorTree.V10.PrefixReplicaPartial
import SuccessorTree.V10.SignatureCollision
import Mathlib.Tactic

/-!
# Forbidden-free preservation for the one-filler type replica

In the one-filler replica, every vertex except the neutral filler
has a unique original address: old socle coordinates map to
themselves, and the relocated type vertex maps to v. Since
d <= freeLevel_A(v) <= v, this address map is increasing on
the replica's non-filler vertices.

Thus every induced, ordered forbidden L-copy avoiding the filler
projects back into A. A nontrivial irreducible forbidden structure
cannot contain the filler, because all its L-pairs are linked,
whereas the filler has no incident L-relation. The two facts
together establish preservation of every forbidden configuration
of size at least two.

The allowed neutral singleton handles forbidden structures of
size one; its exclusion is deliberately tracked separately.
The empty forbidden structure is excluded from the assumptions.
-/

namespace SuccessorTree.V10

/-- The actual address in A of each non-filler replica vertex. -/
def prefixReplicaProject (d v x : Nat) : Nat :=
  if x < d then x else v

theorem prefixReplicaProject_address
    (d v x : Nat)
    (hx : x < d + 2) (hFill : x ≠ d) :
    prefixReplicaAddress d v x =
      some (prefixReplicaProject d v x) := by
  by_cases hOld : x < d
  · simp [prefixReplicaAddress, prefixReplicaProject, hOld]
  · have hLast : x = d + 1 := by omega
    simp [prefixReplicaAddress, prefixReplicaProject, hOld, hLast]

theorem prefixReplicaProject_strictMono_on
    (d v x y : Nat)
    (hdv : d ≤ v)
    (hx : x < d + 2) (hy : y < d + 2)
    (hfx : x ≠ d) (hfy : y ≠ d)
    (hxy : x < y) :
    prefixReplicaProject d v x <
      prefixReplicaProject d v y := by
  by_cases hOldX : x < d
  · by_cases hOldY : y < d
    · simpa [prefixReplicaProject, hOldX, hOldY] using hxy
    · have hLastY : y = d + 1 := by omega
      simp only [prefixReplicaProject, if_pos hOldX, if_neg hOldY]
      omega
  · have hLastX : x = d + 1 := by omega
    omega

/-- A forbidden pattern in a binary language is irreducible if every
two distinct vertices participate in some directed binary relation. -/
def ForbiddenAtomicPattern.Irreducible
    {r db du dd : Nat}
    (F : ForbiddenAtomicPattern r db du dd) : Prop :=
  ∀ a b : Fin r, a ≠ b →
    ∃ t : Fin db, F.binary a b t = true ∨
      F.binary b a t = true

/-- Every nontrivial irreducible forbidden copy in the replica omits
its completely L-isolated filler. -/
theorem irreducible_replica_copy_avoids_filler
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r)
    (hIrred : F.Irreducible)
    (d v : Nat)
    (f : Fin r → Nat)
    (hCopy : (prefixReplicaL A d v).Realizes F f) :
    ∀ a : Fin r, f a ≠ d := by
  have hBinary := hCopy.2.2.1
  let zero : Fin r := ⟨0, by omega⟩
  let one : Fin r := ⟨1, hr⟩
  intro a hFa
  obtain ⟨b, hab⟩ : ∃ b : Fin r, a ≠ b := by
    by_cases ha : a = zero
    · refine ⟨one, ?_⟩
      intro heq
      have hzo : zero = one := ha.symm.trans heq
      have hv := congrArg Fin.val hzo
      norm_num [zero, one] at hv
    · exact ⟨zero, ha⟩
  obtain ⟨t, hPair⟩ := hIrred a b hab
  have hPreserved := hBinary a b hab t
  rw [hFa] at hPreserved
  have hNeutral :=
    (prefixReplicaL_filler_neutral A d v (f b)).1 t
  rcases hPair with hPair | hPair
  · have hz := hNeutral.1
    rw [hz, hPair] at hPreserved
    contradiction
  · have hz := hNeutral.2
    have hPreservedReverse := hBinary b a hab.symm t
    rw [hFa, hz, hPair] at hPreservedReverse
    contradiction

/-- Any copy in the replica omitting the filler projects to an
induced ordered copy in the original A. The increasing-order proof
uses d <= v, and no relation or age assumption is hidden here. -/
theorem replica_copy_projects_to_original
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (v d : Nat)
    (hv : v < A.size)
    (hd : d ≤ A.freeLevel v)
    (f : Fin r → Nat)
    (hCopy : (prefixReplicaL A d v).Realizes F f)
    (hNoFiller : ∀ a : Fin r, f a ≠ d) :
    A.L.Realizes F
      (fun a => prefixReplicaProject d v (f a)) := by
  obtain ⟨hMono, hIn, hBinary, hUnary, hDiagonal⟩ := hCopy
  have hdv : d ≤ v := hd.trans (A.freeLevel_le v)
  have hSize : d ≤ A.size := hdv.trans (Nat.le_of_lt hv)
  have hDomain (a : Fin r) : f a < d + 2 := hIn a
  have hAddress (a : Fin r) :
      prefixReplicaAddress d v (f a) =
        some (prefixReplicaProject d v (f a)) :=
    prefixReplicaProject_address d v (f a) (hDomain a) (hNoFiller a)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact prefixReplicaProject_strictMono_on
      d v (f a) (f b) hdv
      (hDomain a) (hDomain b)
      (hNoFiller a) (hNoFiller b) (hMono hab)
  · intro a
    apply (A.carrier_iff (prefixReplicaProject d v (f a))).2
    by_cases hOld : f a < d
    · simpa [prefixReplicaProject, hOld] using
        (lt_of_lt_of_le hOld hSize)
    · have hLast : f a = d + 1 := by
        have hF := hNoFiller a
        have hD := hDomain a
        omega
      simpa [prefixReplicaProject, hOld] using hv
  · intro a b hab t
    calc
      A.L.binary
          (prefixReplicaProject d v (f a))
          (prefixReplicaProject d v (f b)) t =
          (prefixReplicaL A d v).binary (f a) (f b) t := by
            simp [prefixReplicaL, hAddress a, hAddress b]
      _ = F.binary a b t := hBinary a b hab t
  · intro a t
    calc
      A.L.unary (prefixReplicaProject d v (f a)) t =
          (prefixReplicaL A d v).unary (f a) t := by
            simp [prefixReplicaL, hAddress a]
      _ = F.unary a t := hUnary a t
  · intro a t
    calc
      A.L.diagonal (prefixReplicaProject d v (f a)) t =
          (prefixReplicaL A d v).diagonal (f a) t := by
            simp [prefixReplicaL, hAddress a]
      _ = F.diagonal a t := hDiagonal a t

/-- A nontrivial irreducible forbidden pattern cannot arise in
the one-filler replica unless it already occurred in the source. -/
theorem prefixReplicaL_preserves_avoidance_nontrivial
    {r db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r)
    (hIrred : F.Irreducible)
    (v d : Nat)
    (hv : v < A.size)
    (hd : d ≤ A.freeLevel v)
    (hAvoid : ¬ ∃ f : Fin r → Nat, A.L.Realizes F f) :
    ¬ ∃ f : Fin r → Nat,
      (prefixReplicaL A d v).Realizes F f := by
  rintro ⟨f, hCopy⟩
  have hNoFiller :=
    irreducible_replica_copy_avoids_filler A F hr hIrred d v f hCopy
  exact hAvoid ⟨_, replica_copy_projects_to_original
    A F v d hv hd f hCopy hNoFiller⟩


/-- A singleton is non-neutral if at least one unary or diagonal
binary atom holds. The one-filler replica uses the neutral singleton,
so an explicitly forbidden non-neutral singleton cannot map there. -/
def ForbiddenAtomicPattern.NonNeutralSingleton
    {db du dd : Nat}
    (F : ForbiddenAtomicPattern 1 db du dd) : Prop :=
  (∃ t : Fin du, F.unary 0 t = true) ∨
    (∃ t : Fin dd, F.diagonal 0 t = true)

/-- A forbidden non-neutral singleton in the replica cannot be the
neutral filler; any other singleton projects to the original. -/
theorem nonNeutral_singleton_replica_copy_avoids_filler
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern 1 db du dd)
    (hNonNeutral : F.NonNeutralSingleton)
    (d v : Nat)
    (f : Fin 1 → Nat)
    (hCopy : (prefixReplicaL A d v).Realizes F f) :
    ∀ a : Fin 1, f a ≠ d := by
  intro a
  have ha : a = 0 := Fin.eq_zero a
  subst a
  intro hFill
  rcases hNonNeutral with ⟨t, hPositive⟩ | ⟨t, hPositive⟩
  · have hPreserved := hCopy.2.2.2.1 0 t
    have hNeutral :=
      (prefixReplicaL_filler_neutral A d v (f 0)).2.1 t
    rw [hFill, hNeutral, hPositive] at hPreserved
    contradiction
  · have hPreserved := hCopy.2.2.2.2 0 t
    have hNeutral :=
      (prefixReplicaL_filler_neutral A d v (f 0)).2.2 t
    rw [hFill, hNeutral, hPositive] at hPreserved
    contradiction

/-- Forbidden non-neutral singletons stay forbidden after the
one-neutral-filler replica, assuming they were absent in the source. -/
theorem prefixReplicaL_preserves_avoidance_singleton
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (F : ForbiddenAtomicPattern 1 db du dd)
    (hNonNeutral : F.NonNeutralSingleton)
    (v d : Nat)
    (hv : v < A.size)
    (hd : d ≤ A.freeLevel v)
    (hAvoid : ¬ ∃ f : Fin 1 → Nat, A.L.Realizes F f) :
    ¬ ∃ f : Fin 1 → Nat,
      (prefixReplicaL A d v).Realizes F f := by
  rintro ⟨f, hCopy⟩
  have hNoFiller :=
    nonNeutral_singleton_replica_copy_avoids_filler
      A F hNonNeutral d v f hCopy
  exact hAvoid ⟨_, replica_copy_projects_to_original
    A F v d hv hd f hCopy hNoFiller⟩

end SuccessorTree.V10
