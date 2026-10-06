import SuccessorTree.RamseySpace.Ellentuck
import SuccessorTree.ShapeFiniteRamsey

/-!
# Normalized Ellentuck amalgamation

The manuscript formulates (EA) after normalising the outer map to the
identity.  This file proves that formulation equivalent to the invariant
A3(2) interface used by `shapeEllentuck`.

The key elementary fact is left cancellation: because every M-map is
injective, a finite factor of `G` through the identity is exactly the same
finite factor of `B ∘ G` through `B`.  Hence depths are unchanged by
left composition.
-/

namespace SuccessorTree
namespace SMTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Finite factorisation is invariant under left composition by an injective
outer M-map. -/
theorem ramseyLeFin_comp_left_iff
    (H : SMTree S) (B G : MMap H) (n d : Nat) :
    RamseyLeFin H
        ((ramseyApproximationSystem H).finiteApprox n G)
        ((ramseyApproximationSystem H).finiteApprox d (MMap.id H)) ↔
      RamseyLeFin H
        ((ramseyApproximationSystem H).finiteApprox n (MMap.comp H B G))
        ((ramseyApproximationSystem H).finiteApprox d B) := by
  cases n with
  | zero =>
      simp [RamseyLeFin]
  | succ n =>
      cases d with
      | zero =>
          simp [RamseyLeFin]
      | succ d =>
          constructor
          · intro h
            rcases h with ⟨fac⟩
            refine ⟨{
              map := fac.map
              bound := fac.bound
              agrees := ?_
            }⟩
            intro x
            have hx := fac.agrees x
            change G x.1 = fac.map x.1 at hx
            change B (G x.1) = B (fac.map x.1)
            exact congrArg B hx
          · intro h
            rcases h with ⟨fac⟩
            refine ⟨{
              map := fac.map
              bound := fac.bound
              agrees := ?_
            }⟩
            intro x
            have hx := fac.agrees x
            change B (G x.1) = B (fac.map x.1) at hx
            change G x.1 = fac.map x.1
            exact B.map.injective hx

/-- Abstract depth is invariant under left composition.  This is the formal
version of `depth_B(Bp) = depth_Id(p)`. -/
theorem shapeHasDepth_comp_left_iff
    (H : SMTree S) (B G : MMap H)
    (n d : Nat) :
    (ramseyFinitization H).HasDepth
        (ramseyApprox H n G) (MMap.id H) d ↔
      (ramseyFinitization H).HasDepth
        (ramseyApprox H n (MMap.comp H B G)) B d := by
  constructor
  · intro hd
    constructor
    · exact (ramseyLeFin_comp_left_iff H B G n d).1 hd.1
    · intro e he hfin
      exact hd.2 e he ((ramseyLeFin_comp_left_iff H B G n e).2 hfin)
  · intro hd
    constructor
    · exact (ramseyLeFin_comp_left_iff H B G n d).2 hd.1
    · intro e he hfin
      exact hd.2 e he ((ramseyLeFin_comp_left_iff H B G n e).1 hfin)

/-- Equality after left composition can be cancelled already on a finite
approximation. -/
theorem ramseyApprox_comp_cancel_left
    (H : SMTree S) (B G K : MMap H) (n : Nat)
    (h :
      ramseyApprox H n (MMap.comp H B G) =
        ramseyApprox H n (MMap.comp H B K)) :
    ramseyApprox H n G = ramseyApprox H n K := by
  cases n with
  | zero => rfl
  | succ n =>
      apply Subtype.ext
      funext x
      have hv := congrArg Subtype.val h
      change
        (MMap.comp H B G).restrictLe H n =
          (MMap.comp H B K).restrictLe H n at hv
      have hx := congrFun hv x
      change B (G x.1) = B (K x.1) at hx
      exact B.map.injective hx

/-- Manuscript (EA), in normalized approximation-space language.

If `p` has depth `d` below the identity and the cone `[p,G]` is
nonempty, there is a map in the frozen identity cone `[d,Id]` whose
nonempty `p`-cone is contained in `[p,G]`.

For a nonempty finite map, `d` is one plus its last image level, matching
the manuscript's indexing convention. -/
def ShapeNormalizedEA (H : SMTree S) : Prop :=
  ∀ {n : Nat} (p : RamseyApprox H n) {d : Nat},
    (ramseyFinitization H).HasDepth p (MMap.id H) d →
    ∀ G : MMap H,
      ((ramseyApproximationSystem H).neighborhood p G).Nonempty →
      ∃ K : MMap H,
        K ∈ (ramseyApproximationSystem H).levelNeighborhood d (MMap.id H) ∧
        ((ramseyApproximationSystem H).neighborhood p K).Nonempty ∧
        (ramseyApproximationSystem H).neighborhood p K ⊆
          (ramseyApproximationSystem H).neighborhood p G

/-- Normalized EA implies invariant A3(2). -/
theorem shapeEllentuckAmalgamation_of_normalized
    (H : SMTree S)
    (hEA : ShapeNormalizedEA H) :
    ShapeEllentuckAmalgamation H := by
  intro n a B d hd A hA
  obtain ⟨G, hAG⟩ := mmap_eq_comp_of_ramseyReduction H hA.1
  have haBG :
      ramseyApprox H n (MMap.comp H B G) = a := by
    rw [← hAG]
    exact hA.2
  let p : RamseyApprox H n := ramseyApprox H n G
  have hdp : (ramseyFinitization H).HasDepth p (MMap.id H) d := by
    apply (shapeHasDepth_comp_left_iff H B G n d).2
    simpa only [p, haBG] using hd
  have hpG :
      ((ramseyApproximationSystem H).neighborhood p G).Nonempty := by
    exact ⟨G, ramseyReduction_refl H G, rfl⟩
  obtain ⟨K, hKid, hpK, hsub⟩ := hEA p hdp G hpG
  let A' : MMap H := MMap.comp H B K
  have hA'B : RamseyReduction H A' B := by
    exact ⟨K, fun _ => rfl⟩
  have hA'approx :
      ramseyApprox H d A' = ramseyApprox H d B := by
    have hKidApprox :
        ramseyApprox H d K = ramseyApprox H d (MMap.id H) := hKid.2
    have hcomp :=
      H.ramseyApprox_comp_congr B hKidApprox
    simpa [A'] using hcomp
  refine ⟨A', ⟨hA'B, hA'approx⟩, ?_⟩
  intro X hXaA'
  obtain ⟨Q, hXQ⟩ := mmap_eq_comp_of_ramseyReduction H hXaA'.1
  let R : MMap H := MMap.comp H K Q
  have hXR : X = MMap.comp H B R := by
    rw [hXQ]
    apply MMap.ext_apply
    intro x
    rfl
  have hpR : ramseyApprox H n R = p := by
    have hXB :
        ramseyApprox H n (MMap.comp H B R) =
          ramseyApprox H n (MMap.comp H B G) := by
      rw [← hXR, haBG, hXaA'.2]
    exact (ramseyApprox_comp_cancel_left H B R G n hXB)
  have hRpK :
      R ∈ (ramseyApproximationSystem H).neighborhood p K := by
    refine ⟨?_, hpR⟩
    exact ⟨Q, fun _ => rfl⟩
  have hRpG := hsub hRpK
  rcases hRpG.1 with ⟨Q', hRQ'⟩
  constructor
  · refine ⟨Q', ?_⟩
    intro x
    rw [hXR, hAG]
    change B (R x) = B (G (Q' x))
    exact congrArg B (hRQ' x)
  · exact hXaA'.2

/-- Invariant A3(2), together with the already proved A3(1), gives the
normalized manuscript EA condition. -/
theorem normalized_of_shapeEllentuckAmalgamation
    (H : SMTree S)
    (hEA : ShapeEllentuckAmalgamation H) :
    ShapeNormalizedEA H := by
  intro n p d hd G hpG
  rcases hpG with ⟨X, hXpG⟩
  have hXid :
      X ∈ (ramseyApproximationSystem H).neighborhood p (MMap.id H) := by
    exact ⟨⟨X, fun _ => rfl⟩, hXpG.2⟩
  obtain ⟨K, hKid, hsubX⟩ := hEA p (MMap.id H) hd hXid
  have hpK :
      ((ramseyApproximationSystem H).neighborhood p K).Nonempty :=
    fusionNeighborhood_nonempty H p (MMap.id H) hd hKid
  refine ⟨K, hKid, hpK, ?_⟩
  intro Y hYpK
  have hYpX := hsubX hYpK
  exact (ramseyApproximationSystem H).neighborhood_mono hXpG.1 hYpX

/-- The normalized manuscript condition and abstract A3(2) are equivalent. -/
theorem shapeNormalizedEA_iff
    (H : SMTree S) :
    ShapeNormalizedEA H ↔ ShapeEllentuckAmalgamation H :=
  ⟨shapeEllentuckAmalgamation_of_normalized H,
    normalized_of_shapeEllentuckAmalgamation H⟩

/-- The optional Ellentuck theorem stated directly from normalized EA. -/
theorem shapeEllentuck_of_normalizedEA
    (H : SMTree S) (hEA : ShapeNormalizedEA H) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := ramseyApproximationSystem H) :=
  shapeEllentuck H (shapeEllentuckAmalgamation_of_normalized H hEA)

end SMTree
end SuccessorTree
