import SuccessorTree.RamseySpace.Finitization
import RamseySpace.Axioms

/-!
# Amalgamation for the successor-tree Ramsey space

The first amalgamation axiom is already forced by the finite-factor
interpretation of depth: a witness that `a ≤fin r_d(B)` is a total M-map,
so it can be composed into any `A ∈ [d,B]`.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Todorčević A.3(1) for successor-tree M-maps. -/
theorem ramseyAmalgamation_nonempty
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
          change RamseyLeFin H
            ⟨n + 1, a⟩
            ((ramseyApproximationSystem H).finiteApprox 0 B) at hd
          change False at hd
          contradiction
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
