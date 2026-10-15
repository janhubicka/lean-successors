import SuccessorTree.V10.M2ShapeMapCompatReflection
import SuccessorTree.V10.ParameterLetterUniqueness
import Mathlib.Tactic

/-!
# Pull back a genuine Kpt successor's last ordinary E/L column

The missing concrete E1 step should use the existing M2
\`PartialTypeWithE.reindexOrdinary\` API, not duplicate it.

A genuine target successor type Q at level ell+1 has a
\`ValidNewOrdinaryColumn Q g\`: its last ordinary E-column has first
missing coordinate g, reverse E bits vanish and all directed binary
L relations outside the E-socle are absent. Reindex the old ordinary
coordinates by a strictly increasing rho, retaining the last ordinary
vertex as the last ordinary vertex of a source type of level n+1.

If the preimage of the target cut g is exactly the source initial
segment [0,f), then the source's ACTUAL reindexed last column is
\`ValidNewOrdinaryColumn ... f\`. No E3, age or compatibility hypothesis
is added. The preimage-cut identity is the explicit next obligation
to derive from the *actual* target canonical parameter and the level
map of the given root-preserving Kpt ShapeMap.
-/

namespace SuccessorTree.V10

/-- The canonical last ordinary E/free-cut and no-new-tuples
conditions are stable under a retained-coordinate reindexing,
provided the new vertex is literally retained as the final ordinary
coordinate and the target free cut has precisely the specified
initial-segment preimage.

The conclusion is about the *actual* existing reindexing operation,
not a new structure or the unproved global OneLevelPullback axiom. -/
theorem PartialTypeWithE.reindexOrdinary_validNewColumn
    {n ell db du dd : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (rho : Fin (n + 1) → Fin (ell + 1))
    (hMono : StrictMono rho)
    (hLast : rho (Fin.last n) = Fin.last ell)
    (g : Nat) (hValid : ValidNewOrdinaryColumn Q g)
    (f : Nat)
    (hCut : ∀ i : Fin n,
      ((rho (i.castSucc)).val < g ↔ i.val < f)) :
    ValidNewOrdinaryColumn (Q.reindexOrdinary rho) f := by
  have hEarlier (i : Fin n) :
      (rho i.castSucc).val < ell := by
    have hh := hMono (Fin.castSucc_lt_last i)
    rw [hLast] at hh
    exact hh
  have hRetained (i : Fin n) :
      rho i.castSucc =
        (⟨(rho i.castSucc).val, hEarlier i⟩ : Fin ell).castSucc := by
    apply Fin.ext
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let j : Fin ell := ⟨(rho i.castSucc).val, hEarlier i⟩
    change Q.eRelation (some (rho i.castSucc))
      (some (rho (Fin.last n))) = decide (i.val < f)
    rw [hLast, hRetained i, hValid.oldToNewE j]
    have hIff : j.val < g ↔ i.val < f := hCut i
    by_cases hi : i.val < f
    · have hj : j.val < g := hIff.mpr hi
      simp [hi, hj]
    · have hj : ¬ j.val < g := fun h => hi (hIff.mp h)
      simp [hi, hj]
  · intro i
    let j : Fin ell := ⟨(rho i.castSucc).val, hEarlier i⟩
    change Q.eRelation (some (rho (Fin.last n)))
      (some (rho i.castSucc)) = false
    rw [hLast, hRetained i]
    exact hValid.newToOldE j
  · intro i hi r
    let j : Fin ell := ⟨(rho i.castSucc).val, hEarlier i⟩
    have hj : g ≤ j.val := by
      have hn : ¬ (rho i.castSucc).val < g := by
        intro h
        exact (Nat.not_lt.mpr hi) ((hCut i).mp h)
      change g ≤ (rho i.castSucc).val
      exact Nat.le_of_not_gt hn
    change
      Q.lReduct.binary (some (rho i.castSucc))
        (some (rho (Fin.last n))) r = false ∧
      Q.lReduct.binary (some (rho (Fin.last n)))
        (some (rho i.castSucc)) r = false
    rw [hLast, hRetained i]
    exact hValid.noNewBinaryBeyondCut j hj r

end SuccessorTree.V10
