import Mathlib

namespace SuccessorTree.BANANA

/-- The cancellation identity behind the coherent-EPPA transport
construction in the BANANA manuscript. -/
theorem conjugated_transport_comp {G : Type*} [Group G]
    (gU gV gW ρp ρq : G) :
    (gW * ρq * gV⁻¹) * (gV * ρp * gU⁻¹) =
      gW * (ρq * ρp) * gU⁻¹ := by
  group

/-- If the middle factors come from a group homomorphism, the transported
extensions compose exactly as required for coherent EPPA. -/
theorem coherent_transport {α H G : Type*} [Group H] [Group G]
    (ρ : H →* G) (g : α → G)
    (U V W : α) (p q : H) :
    (g W * ρ q * (g V)⁻¹) * (g V * ρ p * (g U)⁻¹) =
      g W * ρ (q * p) * (g U)⁻¹ := by
  rw [map_mul]
  exact conjugated_transport_comp (g U) (g V) (g W) (ρ p) (ρ q)

end SuccessorTree.BANANA
