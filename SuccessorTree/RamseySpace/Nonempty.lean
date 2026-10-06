import SuccessorTree.RamseySpace.Finitization

/-!
# Nonempty finite neighborhoods for direct fusion

This is Todorcevic A.3(1), but it is only a finite-factorization fact for
successor-tree M-maps.  It is used by the ordinary finite-dimensional fusion
proof and is intentionally separated from A.3(2)/EA.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- If a finite approximation has depth d in B, then it remains realizable
inside every refinement which agrees with B through depth d. -/
theorem fusionNeighborhood_nonempty
    (H : SMTree S)
    {n : Nat} (a : (ramseyApproximationSystem H).Approx n)
    (B : MMap H) {d : Nat}
    (hd : (ramseyFinitization H).HasDepth a B d) :
    ∀ ⦃A : MMap H⦄,
      A ∈ (ramseyApproximationSystem H).levelNeighborhood d B →
        ((ramseyApproximationSystem H).neighborhood a A).Nonempty := by
  intro A hA
  cases n with
  | zero =>
      refine ⟨A, ramseyReduction_refl H A, ?_⟩
      cases a
      rfl
  | succ n =>
      cases d with
      | zero =>
          have hfin :
              RamseyLeFin H
                ⟨n + 1, a⟩
                ((ramseyApproximationSystem H).finiteApprox 0 B) := by
            simpa [ramseyFinitization] using hd.1
          have hle : n + 1 ≤ 0 :=
            ramseyLeFin_level_le H hfin
          omega
      | succ d =>
          have hfin :
              RamseyLeFin H
                ⟨n + 1, a⟩
                ⟨d + 1, ramseyApprox H (d + 1) B⟩ := hd.1
          rcases hfin with ⟨fac⟩
          let X : MMap H := MMap.comp H A fac.map
          refine ⟨X, ?_, ?_⟩
          · refine ⟨fac.map, ?_⟩
            intro x
            rfl
          · apply Subtype.ext
            change X.restrictLe H n = a.1
            funext x
            have hAB := congrArg Subtype.val hA.2
            change A.restrictLe H d = B.restrictLe H d at hAB
            have hABx :
                A (fac.map x.1) = B (fac.map x.1) := by
              exact congrFun hAB ⟨fac.map x.1, fac.bound x⟩
            have hagree := fac.agrees x
            change a.1 x = B (fac.map x.1) at hagree
            change A (fac.map x.1) = a.1 x
            exact hABx.trans hagree.symm

end SMTree
end SuccessorTree
