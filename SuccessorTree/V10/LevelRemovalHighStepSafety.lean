import SuccessorTree.V10.LevelRemovalUniformLevel
import SuccessorTree.V10.LevelRemovalGapColumn
import SuccessorTree.V10.EmptyParameterS2
import Mathlib.Tactic

/-!
# The genuine mapped successor satisfies the sharp deletion safety case split

For the upper-base weak successor part of M2, deleting the last target
level missing immediately before F(a0) shortens the *old* canonical
one-step output. The finite reconstruction theorem requires either
m < k, so the coordinate lies strictly below its last predecessor
position, OR the new canonical E cut f is strictly below m.

The first disjunct follows when the source base is above a0 by
strict image-level monotonicity. At the boundary source level a0,
the canonical parameter list of an actual mapped successor is exactly
the image of the old parameter list; S1 and the gap imply that all
its members are below m. The empty-parameter case forces f=0;
in the nonempty case its singleton parameter has level f. Hence
f<m, with no added free-cut hypothesis.

This lemma makes the previously hidden boundary condition explicit.
It does NOT assume or prove the weak successor law of the deleted map,
its injectivity, or M2 factorization.
-/

namespace SuccessorTree.V10

/-- For a canonical successor of F(a), if the source base lies at or
above the first affected source level, the fixed deletion coordinate
m=lev(F(a0))-1 satisfies the exact finite canonical-step safety
condition m<k or f<m (where lev(F(a))=k+1).

The source parameters are those of a genuine successor of a, and
the canonical parameter option is that of its actual mapped step.
No M2 or additional E-age condition is required. -/
theorem mapped_upper_canonical_step_safe_for_gap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (q₀ a₀ a b : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hPrev : LevelTree.lev q₀ + 1 = LevelTree.lev a₀)
    (hGap : LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a₀))
    (hHigh : LevelTree.lev a₀ ≤ LevelTree.lev a)
    (hSucc : (admissibleKptSTree family).succ a p c = some b)
    (k f : Nat) (hf : f ≤ k + 1)
    (Q : PartialTypeWithE (k + 2) db du dd)
    (hBase :
      (F a).1 =
        (⟨k + 1, Q.restrict (Nat.le_succ (k + 1))⟩ :
          RawPartialTypeNode db du dd))
    (hParam :
      (p.map F).map (fun x => x.1) =
        (Q.canonicalParameterRecord f hf).toList) :
    let m := LevelTree.lev (F a₀) - 1
    m < k ∨ f < m := by
  classical
  let m : Nat := LevelTree.lev (F a₀) - 1
  change m < k ∨ f < m
  have hFLevel : LevelTree.lev (F a) = k + 1 := by
    have hh := congrArg Sigma.fst hBase
    exact hh
  have hFLe : LevelTree.lev (F a₀) ≤ LevelTree.lev (F a) :=
    shapeMap_level_le_of_level_le family F hHigh
  have hMPos : 0 < m := by
    dsimp [m]
    omega
  by_cases hmk : m < k
  · exact Or.inl hmk
  · right
    have hFEqual : LevelTree.lev (F a) = LevelTree.lev (F a₀) := by
      dsimp [m] at hmk
      omega
    have hSourceEqual : LevelTree.lev a = LevelTree.lev a₀ := by
      by_contra hne
      have hgt : LevelTree.lev a₀ < LevelTree.lev a := by omega
      have hstrict := F.level_lt_of_level_lt hgt
      omega
    have hPrevA : LevelTree.lev q₀ + 1 = LevelTree.lev a := by
      omega
    have hGapA :
        LevelTree.lev (F q₀) + 1 < LevelTree.lev (F a) := by
      rw [hFEqual]
      exact hGap
    have hMappedBound : ∀ y ∈ p.map F, LevelTree.lev y < m := by
      intro y hy
      obtain ⟨x,hx,hxy⟩ := List.mem_map.mp hy
      subst y
      have hBound := mapped_successor_parameters_below_gap
        family F q₀ a b p c hPrevA hGapA hSucc x hx
      simpa only [hFEqual, m] using hBound
    by_cases hfZero : f = 0
    · omega
    · have hMember :
          (⟨f,Q.lastOrdinaryParameter f hf⟩ :
            RawPartialTypeNode db du dd) ∈
            (p.map F).map (fun x => x.1) := by
        rw [hParam]
        simp [PartialTypeWithE.canonicalParameterRecord, hfZero]
      obtain ⟨y,hy,hyRecord⟩ := List.mem_map.mp hMember
      have hYLevel : LevelTree.lev y = f := by
        change y.1.1 = f
        exact congrArg Sigma.fst hyRecord
      have hYSmall := hMappedBound y hy
      omega

end SuccessorTree.V10
