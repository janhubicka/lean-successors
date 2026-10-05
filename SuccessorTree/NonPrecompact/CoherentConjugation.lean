import Mathlib.GroupTheory.Group.Basic

/-!
# Conjugated coherent transport

This file isolates the group-theoretic cancellation used at the end of the
BANANA coherent-EPPA proof.

Given a homomorphism rho : H → G and chosen conjugating elements g_U, define
  Theta(U,V,h) = g_V * rho(h) * g_U⁻¹.
Then composition is coherent:
  Theta(V,W,q) * Theta(U,V,p) = Theta(U,W,q*p).
-/

namespace SuccessorTree.NonPrecompact

/-- Conjugate a fixed homomorphic action by object-dependent choices. -/
def conjugatedTransport
    {G H O : Type*} [Group G] [Group H]
    (rho : H →* G) (g : O → G)
    (U V : O) (h : H) : G :=
  g V * rho h * (g U)⁻¹

@[simp]
theorem conjugatedTransport_one
    {G H O : Type*} [Group G] [Group H]
    (rho : H →* G) (g : O → G)
    (U : O) :
    conjugatedTransport rho g U U 1 = 1 := by
  simp [conjugatedTransport]

/-- The conjugation formula preserves composition. -/
theorem conjugatedTransport_mul
    {G H O : Type*} [Group G] [Group H]
    (rho : H →* G) (g : O → G)
    (U V W : O) (p q : H) :
    conjugatedTransport rho g V W q *
        conjugatedTransport rho g U V p =
      conjugatedTransport rho g U W (q * p) := by
  simp [conjugatedTransport, map_mul, mul_assoc]

/-- In particular, inverse-labelled transports are inverse group elements. -/
theorem conjugatedTransport_inv
    {G H O : Type*} [Group G] [Group H]
    (rho : H →* G) (g : O → G)
    (U V : O) (p : H) :
    (conjugatedTransport rho g U V p)⁻¹ =
      conjugatedTransport rho g V U p⁻¹ := by
  simp [conjugatedTransport, mul_assoc]

end SuccessorTree.NonPrecompact
