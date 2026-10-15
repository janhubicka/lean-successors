import SuccessorTree.V10.M2SourceTypeAge
import SuccessorTree.V10.M2ShapeMapCompatReflection
import Mathlib.Tactic

/-!
# Concrete Kpt E1 preparation: induced finite L-age reindexing

If T is a genuine admissible partial L+ type over m ordinary
coordinates and rho : Fin n -> Fin m is strictly increasing, the
existing M2 reflection library's PartialTypeWithE.reindexOrdinary
selects exactly those ordinary coordinates and the type vertex.
The complete record transports all positive/negative L and E bits;
there is NO new reindexing API or duplicate structure.

For the forbidden-family AGE test, only the L reduct matters.
The corresponding ageModel of the pulled-back type admits an
induced ordered embedding into T.ageModel, mapping each
ordinary coordinate i to rho(i) and the distinguished type
vertex to the target type vertex. Thus every normalized
forbidden L-pattern avoided by T is also avoided by the
pulled-back finite L-age model.

Crucially this theorem does NOT assert that arbitrary E
reindexing is spaced or admissible as a partial structure:
the final Kpt one-level pullback E1 must additionally recover
the old source E columns, the new free E-cut from its parameter,
the no-new-tuples rule, and a genuine padded L+ realization.
Those obligations cannot be inferred from L-age avoidance alone.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- The corresponding finite age-model embedding sends source
ordinary coordinate x<n to the retained target coordinate rho(x),
and the source type vertex n to the target type vertex m. -/
def finiteTypeCarrierLift {m : Nat}
    (n : Nat) (rho : Fin n → Fin m) (x : Nat) : Nat :=
  if h : x < n then (rho ⟨x,h⟩).val else m

/-- The carrier embedding agrees EXACTLY with Option-coded
ordinary/type-vertex indices. -/
theorem finiteTypeCarrierLift_typeIndex
    {m : Nat} (n : Nat) (rho : Fin n → Fin m) (x : Nat) :
    typeAgeIndex m (finiteTypeCarrierLift n rho x) =
      (typeAgeIndex n x).map rho := by
  by_cases hx : x < n
  · simp [finiteTypeCarrierLift, typeAgeIndex, hx]
  · simp [finiteTypeCarrierLift, typeAgeIndex, hx]

/-- The whole induced L reduct of an ordinary-coordinate pullback
embeds into the target's actual finite type-age model.
No E relation is attached to the forbidden L-structure. -/
def PartialTypeWithE.reindexOrdinary_ageEmbedding
    {m : Nat}
    (T : PartialTypeWithE m db du dd)
    (n : Nat) (rho : Fin n → Fin m)
    (hMono : StrictMono rho) :
    (T.reindexOrdinary rho).ageModel.InducedEmbeddingOnCarrier
      T.ageModel where
  toFun := finiteTypeCarrierLift n rho
  order := by
    intro x y hx hy hxy
    change x ≤ n at hx
    change y ≤ n at hy
    by_cases hy0 : y < n
    · have hx0 : x < n := by omega
      have hxyFin : (⟨x,hx0⟩ : Fin n) < ⟨y,hy0⟩ := hxy
      have hLt := hMono hxyFin
      simpa [finiteTypeCarrierLift, hx0,hy0] using hLt
    · have hyEq : y = n := by omega
      have hx0 : x < n := by omega
      subst y
      simpa [finiteTypeCarrierLift, hx0] using
        (rho ⟨x,hx0⟩).isLt
  inside := by
    intro x hx
    change x ≤ n at hx
    change finiteTypeCarrierLift n rho x ≤ m
    by_cases h : x < n
    · simp [finiteTypeCarrierLift, h]
    · simp [finiteTypeCarrierLift, h]
  binary := by
    intro x y hx hy hne t
    change T.lReduct.binary
        (typeAgeIndex m (finiteTypeCarrierLift n rho x))
        (typeAgeIndex m (finiteTypeCarrierLift n rho y)) t =
      T.lReduct.binary
        ((typeAgeIndex n x).map rho)
        ((typeAgeIndex n y).map rho) t
    rw [finiteTypeCarrierLift_typeIndex n rho x,
      finiteTypeCarrierLift_typeIndex n rho y]
  unary := by
    intro x hx t
    change T.lReduct.unary
        (typeAgeIndex m (finiteTypeCarrierLift n rho x)) t =
      T.lReduct.unary ((typeAgeIndex n x).map rho) t
    rw [finiteTypeCarrierLift_typeIndex n rho x]
  diagonal := by
    intro x hx t
    change T.lReduct.diagonal
        (typeAgeIndex m (finiteTypeCarrierLift n rho x)) t =
      T.lReduct.diagonal ((typeAgeIndex n x).map rho) t
    rw [finiteTypeCarrierLift_typeIndex n rho x]

/-- A genuine admissible target Kpt type transfers forbidden L-age
avoidance to any strictly increasing finite list of retained old
coordinates plus the distinguished type vertex. -/
theorem PartialTypeWithE.reindexOrdinary_age_avoids
    {m : Nat}
    (family : List (NormalizedForbidden db du dd))
    (T : PartialTypeWithE m db du dd)
    (n : Nat) (rho : Fin n → Fin m)
    (hMono : StrictMono rho)
    (hAd : IsAdmissibleRawType family
      (⟨m,T⟩ : RawPartialTypeNode db du dd)) :
    ∀ bad, bad ∈ family →
      bad.Avoids (T.reindexOrdinary rho).ageModel :=
  (T.reindexOrdinary_ageEmbedding n rho hMono).preserves_avoidance
    family (T.ageModel_avoids family hAd)

end SuccessorTree.V10
