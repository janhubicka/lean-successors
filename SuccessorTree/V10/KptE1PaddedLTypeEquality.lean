import SuccessorTree.V10.KptE1NeutralSourceAge
import Mathlib.Tactic

/-!
# The padded E1 source has exactly the original complete L type

The neutral-spacer source model was previously proved forbidden-L free.
It is not enough to know there is an induced embedding: canonical
successor reconstruction requires literal equality of all L-reduct
atoms on the ordinary prefix and the distinguished type vertex.

The embedding sends every original ordinary coordinate i<=n to i,
and moves the original type index n+1 to the new witness n+2.
Every such source index is an ACTUAL vertex of the sparse source,
so neutral filling changes none of its binary, unary, or diagonal
records. Thus the induced L type extracted at cut n+1 from witness
n+2 agrees exactly with the given partial type's L-reduct.
No auxiliary E is transported onto forbidden L-age witnesses.
-/

namespace SuccessorTree.V10

/-- The correct sparse-source index, read back in Q's original L age,
is literally the original option-coded coordinate. -/
theorem e1PaddedAgeIndex_option
    (n : Nat) (x : Option (Fin (n + 1))) :
    typeAgeIndex (n + 1)
      (e1PaddedAgeIndex n (prefixVertexIndex (n + 2) x)) = x := by
  cases x with
  | none =>
      simp [prefixVertexIndex, e1PaddedAgeIndex, typeAgeIndex]
  | some i =>
      have hi : i.val ≤ n := by omega
      simp [prefixVertexIndex, e1PaddedAgeIndex, typeAgeIndex, hi]

/-- Every literal ordinary/type source coordinate is REAL in the sparse
induced model and therefore survives neutral filling unchanged. -/
theorem e1PaddedReal_option
    (n : Nat) (x : Option (Fin (n + 1))) :
    prefixVertexIndex (n + 2) x < n + 3 ∧
      e1PaddedReal n (prefixVertexIndex (n + 2) x) := by
  cases x with
  | none =>
      change n + 2 < n + 3 ∧ (n + 2 ≤ n ∨ n + 2 = n + 2)
      omega
  | some i =>
      change i.val < n + 3 ∧ (i.val ≤ n ∨ i.val = n + 2)
      omega

/-- All directed L-binary records (true OR false) agree literally
on the retained original ordinary/type vertices. -/
theorem e1PaddedSourceAge_binary_type
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (x y : Option (Fin (n + 1))) (t : Fin db) :
    (e1PaddedSourceAge Q).binary
      (prefixVertexIndex (n + 2) x) (prefixVertexIndex (n + 2) y) t =
      Q.lReduct.binary x y t := by
  let sparse := Q.ageModel.sparsePullback (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)
  have hx : prefixVertexIndex (n + 2) x ∈ sparse.carrier :=
    e1PaddedReal_option n x
  have hy : prefixVertexIndex (n + 2) y ∈ sparse.carrier :=
    e1PaddedReal_option n y
  calc
    (e1PaddedSourceAge Q).binary
        (prefixVertexIndex (n + 2) x)
        (prefixVertexIndex (n + 2) y) t =
      sparse.binary
        (prefixVertexIndex (n + 2) x)
        (prefixVertexIndex (n + 2) y) t :=
      sparse.fillNeutralCarrier_old_binary (n + 3)
        _ _ hx hy t
    _ = Q.lReduct.binary x y t := by
      change
        Q.lReduct.binary
          (typeAgeIndex (n + 1)
            (e1PaddedAgeIndex n (prefixVertexIndex (n + 2) x)))
          (typeAgeIndex (n + 1)
            (e1PaddedAgeIndex n (prefixVertexIndex (n + 2) y))) t =
        Q.lReduct.binary x y t
      rw [e1PaddedAgeIndex_option n x, e1PaddedAgeIndex_option n y]

/-- Exact unary L data survives the neutral spacer. -/
theorem e1PaddedSourceAge_unary_type
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (x : Option (Fin (n + 1))) (t : Fin du) :
    (e1PaddedSourceAge Q).unary
      (prefixVertexIndex (n + 2) x) t = Q.lReduct.unary x t := by
  let sparse := Q.ageModel.sparsePullback (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)
  have hx : prefixVertexIndex (n + 2) x ∈ sparse.carrier :=
    e1PaddedReal_option n x
  calc
    (e1PaddedSourceAge Q).unary (prefixVertexIndex (n + 2) x) t =
      sparse.unary (prefixVertexIndex (n + 2) x) t :=
      sparse.fillNeutralCarrier_old_unary (n + 3) _ hx t
    _ = Q.lReduct.unary x t := by
      change Q.lReduct.unary
        (typeAgeIndex (n + 1)
          (e1PaddedAgeIndex n (prefixVertexIndex (n + 2) x))) t =
        Q.lReduct.unary x t
      rw [e1PaddedAgeIndex_option n x]

/-- Exact diagonal L data survives the neutral spacer. -/
theorem e1PaddedSourceAge_diagonal_type
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd)
    (x : Option (Fin (n + 1))) (t : Fin dd) :
    (e1PaddedSourceAge Q).diagonal
      (prefixVertexIndex (n + 2) x) t = Q.lReduct.diagonal x t := by
  let sparse := Q.ageModel.sparsePullback (n + 3)
    (e1PaddedReal n) (e1PaddedAgeIndex n)
  have hx : prefixVertexIndex (n + 2) x ∈ sparse.carrier :=
    e1PaddedReal_option n x
  calc
    (e1PaddedSourceAge Q).diagonal (prefixVertexIndex (n + 2) x) t =
      sparse.diagonal (prefixVertexIndex (n + 2) x) t :=
      sparse.fillNeutralCarrier_old_diagonal (n + 3) _ hx t
    _ = Q.lReduct.diagonal x t := by
      change Q.lReduct.diagonal
        (typeAgeIndex (n + 1)
          (e1PaddedAgeIndex n (prefixVertexIndex (n + 2) x))) t =
        Q.lReduct.diagonal x t
      rw [e1PaddedAgeIndex_option n x]

/-- Complete L-type equality at the actual distinguished source witness,
including EVERY negative directed binary table, unary and diagonal bit. -/
theorem e1PaddedSourceAge_complete_L_type
    {db du dd : Nat} {n : Nat}
    (Q : PartialTypeWithE (n + 1) db du dd) :
    RelationalPrefixType.ofAgeModel
      (e1PaddedSourceAge Q) (n + 1) (n + 2) = Q.lReduct := by
  apply RelationalPrefixType.eq_of_atoms
  · intro x y t
    exact e1PaddedSourceAge_binary_type Q x y t
  · intro x t
    exact e1PaddedSourceAge_unary_type Q x t
  · intro x t
    exact e1PaddedSourceAge_diagonal_type Q x t

end SuccessorTree.V10
