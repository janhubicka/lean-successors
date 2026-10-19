import Mathlib.Tactic

/-!
# Level-homogeneous ancestral successor codes

This is the local, finite part of the insertion-stability condition considered
in the v21 successor manuscript. A code is a label and a list of ancestral
indices. The set of legal codes depends on the current level but not on the
history. Legality is stable when an unused level is inserted anywhere among
the indices.

The lemmas below prove two consequences needed by a generic one-gap
construction: insertion preserves ancestral bounds and a legal code remains
legal at every greater level. In particular, a single root code supplies a
legal parameter-free code at every level.

This module does **not** claim to prove M2 or M3 for the corresponding
history tree. Their generic one-gap shape-map construction and the
factorisation step remain to be formalised; the unrestricted free ancestral
instance is already proved in `FreeAncestralSMTree`.
-/

namespace SuccessorTree

/-- Reindex an ancestor when a new level is inserted at `t`. -/
def insertAncestorIndex (t j : Nat) : Nat :=
  if j < t then j else j + 1

/-- Ancestor indices remain below the new source level. -/
theorem insertAncestorIndex_lt {n t j : Nat}
    (hj : j < n) :
    insertAncestorIndex t j < n + 1 := by
  unfold insertAncestorIndex
  split_ifs <;> omega

/-- A level-dependent set of admissible ancestral codes. The insertion
condition explicitly includes insertion *inside* the ancestor list, and is
stronger than persistence along a single branch. -/
structure InsertionStableCodeScheme (Label : Type*) where
  allowed : Nat → Label → List Nat → Prop
  bounded : ∀ {n : Nat} {c : Label} {p : List Nat},
    allowed n c p → ∀ j ∈ p, j < n
  root : ∃ c : Label, allowed 0 c []
  insert : ∀ {n t : Nat} {c : Label} {p : List Nat},
    t ≤ n → allowed n c p →
      allowed (n + 1) c (p.map (insertAncestorIndex t))

namespace InsertionStableCodeScheme

variable {Label : Type*} (S : InsertionStableCodeScheme Label)

private theorem map_insert_end (p : List Nat) (m : Nat) :
    (∀ j ∈ p, j < m) → p.map (insertAncestorIndex m) = p := by
  induction p with
  | nil =>
      intro _
      rfl
  | cons j js ih =>
      intro hp
      have hj : j < m := hp j (by simp)
      have hjs : ∀ k ∈ js, k < m := by
        intro k hk
        exact hp k (by simp [hk])
      simp [insertAncestorIndex, hj, ih hjs]

/-- Inserting unused levels at the end proves ordinary upward persistence. -/
theorem allowed_later {n m : Nat} (hnm : n ≤ m)
    {c : Label} {p : List Nat} (hc : S.allowed n c p) :
    S.allowed m c p := by
  have h : ∀ d : Nat, S.allowed (n + d) c p := by
    intro d
    induction d with
    | zero => simpa using hc
    | succ d ih =>
        have hnew := S.insert (n := n + d) (t := n + d) (le_refl _) ih
        have hm : p.map (insertAncestorIndex (n + d)) = p :=
          map_insert_end p (n + d) (S.bounded ih)
        rw [hm] at hnew
        exact hnew
  simpa [Nat.add_sub_of_le hnm] using h (m - n)

/-- The root's parameter-free code remains usable at every level. -/
theorem exists_parameter_free (m : Nat) :
    ∃ c : Label, S.allowed m c [] := by
  obtain ⟨c, hc⟩ := S.root
  exact ⟨c, S.allowed_later (Nat.zero_le m) hc⟩

end InsertionStableCodeScheme

/-- All ancestral lists of length at most `arity` form an insertion-stable
scheme; this is exactly the finite-code condition for the free ancestral
example (the separately typed free-tree implementation uses `Fin n`). -/
noncomputable def freeAncestralCodeScheme
    (Label : Type*) [Nonempty Label] (arity : Nat) :
    InsertionStableCodeScheme Label where
  allowed := fun n _ p => p.length ≤ arity ∧ ∀ j ∈ p, j < n
  bounded := by
    intro n c p hp j hj
    exact hp.2 j hj
  root := by
    refine ⟨Classical.choice (inferInstance : Nonempty Label), ?_⟩
    simp
  insert := by
    intro n t c p _ht hp
    constructor
    · simpa only [List.length_map] using hp.1
    · intro j hj
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
      exact insertAncestorIndex_lt (hp.2 k hk)

end SuccessorTree
