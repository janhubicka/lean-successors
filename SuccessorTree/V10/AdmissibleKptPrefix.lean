import SuccessorTree.V10.PrefixReplicaAge
import SuccessorTree.V10.RawPrefixOrder
import Mathlib.Tactic

/-!
# Prefix closure of the admissible finite partial-type family

This file packages the exact finite unary/binary analogue of the
paper's Kpt definition. Forbidden structures are enumerated and
irreducible; nontrivial ones have size at least two, while each
forbidden singleton differs from the chosen neutral singleton type.
The empty forbidden structure is excluded.

An admissible raw type is a COMPLETE type extracted at the free
level of a vertex of an enumerated partial structure whose L-reduct
avoids the finite forbidden family.

The one-filler replica constructed in the previous modules now proves
that this family is closed under EVERY initial-socle restriction.
This is the missing membership step between the raw L+ prefix order
and the actual forbidden-free Kpt prefix forest. The proof uses
irreducibility and the allowed neutral singleton rather than
assuming an arbitrary raw finite type is admissible.

Level finiteness and the full Kpt LevelTree/SMTree instances remain
separate formalization targets. The treatment of nullary symbols
must be fixed uniformly at the ambient class level.
-/

namespace SuccessorTree.V10

/-- A forbidden configuration is either a non-neutral singleton or
a nontrivial binary-irreducible enumerated pattern. -/
inductive NormalizedForbidden (db du dd : Nat) where
  | singleton (F : ForbiddenAtomicPattern 1 db du dd)
      (hNeutral : F.NonNeutralSingleton)
  | nontrivial (r : Nat) (F : ForbiddenAtomicPattern r db du dd)
      (hr : 1 < r) (hIrred : F.Irreducible)

/-- A relational model omits a single normalized forbidden pattern.
The absence is an ordered INDUCED embedding condition. -/
def NormalizedForbidden.Avoids
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (L : AgeTestModel db du dd) : Prop :=
  match bad with
  | .singleton F _ =>
      ¬ ∃ f : Fin 1 → Nat, L.Realizes F f
  | .nontrivial r F _ _ =>
      ¬ ∃ f : Fin r → Nat, L.Realizes F f

/-- Every one-filler L replica preserves avoidance of each normalized
forbidden pattern. The cases are precisely the singleton and
irreducible nontrivial age lemmas already proved. -/
theorem NormalizedForbidden.replica_preserves_avoidance
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd)
    (A : EnumeratedPartialStructure db du dd)
    (v d : Nat) (hv : v < A.size)
    (hd : d ≤ A.freeLevel v)
    (hAvoid : bad.Avoids A.L) :
    bad.Avoids (prefixReplicaL A d v) := by
  cases bad with
  | singleton F hNeutral =>
      exact prefixReplicaL_preserves_avoidance_singleton
        A F hNeutral v d hv hd hAvoid
  | nontrivial r F hr hIrred =>
      exact prefixReplicaL_preserves_avoidance_nontrivial
        A F hr hIrred v d hv hd hAvoid

/-- Exactly the finite partial-type family Kpt in the explicit
normalized binary/unary representation: the level is the free
E cut, and its full record is induced from a forbidden-free
ambient partial structure. -/
def IsAdmissibleRawType
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (N : RawPartialTypeNode db du dd) : Prop :=
  ∃ (A : EnumeratedPartialStructure db du dd) (v : Nat),
    v < A.size ∧
    (∀ bad, bad ∈ family → bad.Avoids A.L) ∧
    N = A.rawTypeAtFree v

/-- Core Kpt prefix-closure theorem: if a complete partial type
is represented by a vertex of a forbidden-free partial structure,
then EVERY shorter induced L+ prefix has a representation of the
same kind. One neutral filler suffices to satisfy spacing.

All three E axioms, the exact L-type, the original type's free
cut and preservation of every normalized forbidden pattern
have already been checked independently above. -/
theorem admissibleRawType_closed_under_prefix
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {N : RawPartialTypeNode db du dd}
    (hN : IsAdmissibleRawType family N)
    (d : Nat) (hd : d ≤ N.1) :
    IsAdmissibleRawType family
      (⟨d, N.2.restrict hd⟩ : RawPartialTypeNode db du dd) := by
  obtain ⟨A, v, hv, hAvoid, hNode⟩ := hN
  subst N
  change d ≤ A.freeLevel v at hd
  let B := prefixReplicaPartialStructure A v d hv hd
  have hFree : B.freeLevel (d + 1) = d :=
    prefixReplicaPartialStructure_freeLevel A v d hv hd
  have hType : B.partialTypeAt d (d + 1) =
      A.partialTypeAt d v :=
    prefixReplicaPartialStructure_type_eq A v d hv hd
  have hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L := by
    intro bad hMem
    exact bad.replica_preserves_avoidance A v d hv hd
      (hAvoid bad hMem)
  have hBNode :
      B.rawTypeAtFree (d + 1) =
        (⟨d, A.partialTypeAt d v⟩ : RawPartialTypeNode db du dd) := by
    simp only [EnumeratedPartialStructure.rawTypeAtFree,
      hFree, hType]
  refine ⟨B, d + 1, ?_, hAvoidB, ?_⟩
  · change d + 1 < d + 2
    omega
  · calc
      (⟨d, (A.rawTypeAtFree v).2.restrict hd⟩ :
          RawPartialTypeNode db du dd) =
          ⟨d, A.partialTypeAt d v⟩ := by
            exact congrArg (Sigma.mk d)
              (A.partialTypeAt_restrict d (A.freeLevel v) v hd)
      _ = B.rawTypeAtFree (d + 1) := hBNode.symm

end SuccessorTree.V10
