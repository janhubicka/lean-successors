import SuccessorTree.V10.GPlusAlgorithmFinitePalette
import SuccessorTree.V10.GPlusInducedAction
import Mathlib.Tactic

/-!
# Final V10 transfer: the G+ action is determined by finite Kpt approximations

The manuscript colours finite shape approximations by evaluating their
induced G+ images on bounded representing pairs.

The pair upper node has level at most b. If two genuine Kpt ShapeMaps
F and G agree on ALL Kpt nodes through level b, they agree on BOTH
endpoints of any such pair. Hence their induced actions agree on the
represented G+ vertex, by the ALREADY VERIFIED representative-pair
well-definedness equation. The same holds simultaneously on every
q-tuple from the actual bounded representation palette.

This is the precise independence of total representatives required
when descending a G+ colouring to an AM_b^0 finite approximation.
It uses no abstract action axiom, no envelope existence assumption
and no E1 hypothesis. To finish the colouring pullback one must
combine it with the verified finite approximation representative
agreement and the concrete shape Ramsey action/finite palette.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

/-- Genuine G+ action on a bounded represented source code depends
only on the corresponding finite Kpt source segment. -/
theorem gPlusShapeImage_eq_of_agree_bounded_pair
    (family : List (NormalizedForbidden db du dd))
    (b : Nat)
    (F G : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ b → F x = G x)
    (Q : BoundedGPlusRepresentingPair family b) :
    gPlusShapeImage F Q.val.vertex =
      gPlusShapeImage G Q.val.vertex := by
  have hTop : F Q.val.upper = G Q.val.upper :=
    hAgree Q.val.upper Q.property
  have hLowerBound : LevelTree.lev Q.val.lower ≤ b :=
    (LevelTree.level_le_of_le Q.val.lower_lt_upper.le).trans Q.property
  have hLow : F Q.val.lower = G Q.val.lower :=
    hAgree Q.val.lower hLowerBound
  have hPair : Q.val.image F = Q.val.image G := by
    cases hQ : Q.val with
    | mk lower upper hlt =>
        have hLower : F lower = G lower := by
          simpa [hQ] using hLow
        have hUpper : F upper = G upper := by
          simpa [hQ] using hTop
        simp only [GPlusRepresentingPair.image, hLower, hUpper]
  calc
    gPlusShapeImage F Q.val.vertex = (Q.val.image F).vertex :=
      (Q.val.image_vertex_eq_canonicalShapeImage F).symm
    _ = (Q.val.image G).vertex :=
      congrArg GPlusRepresentingPair.vertex hPair
    _ = gPlusShapeImage G Q.val.vertex :=
      Q.val.image_vertex_eq_canonicalShapeImage G

/-- The same independence on any actual member of the finite
bounded representation palette, not just a chosen representing pair. -/
theorem gPlusShapeImage_eq_of_agree_bounded_palette
    (family : List (NormalizedForbidden db du dd))
    (b : Nat)
    (F G : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ b → F x = G x)
    {A : FiniteGPlusVertex family}
    (hA : A ∈ boundedRepresentableGPlusVertices family b) :
    gPlusShapeImage F A = gPlusShapeImage G A := by
  obtain ⟨Q,hQ⟩ := hA
  subst A
  exact gPlusShapeImage_eq_of_agree_bounded_pair family b F G hAgree Q

/-- Pointwise independence of the total extension for any q-tuple
in the ACTUAL finite bounded G+ palette. -/
theorem gPlusShapeImage_eq_of_agree_bounded_tuple
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    (F G : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hAgree : ∀ x : AdmissibleKptNode family,
      LevelTree.lev x ≤ b → F x = G x)
    (A : Fin q → FiniteGPlusVertex family)
    (hA : A ∈ boundedGPlusTuplePalette family b q) :
    (fun i : Fin q => gPlusShapeImage F (A i)) =
      (fun i : Fin q => gPlusShapeImage G (A i)) := by
  obtain ⟨Q,hQ⟩ := hA
  subst A
  funext i
  exact gPlusShapeImage_eq_of_agree_bounded_pair family b
    F G hAgree (Q i)

/-- Equality of genuine M-map finite approximations at level b+1
is strong enough to identify the induced actions on every
bounded source-palette tuple. -/
theorem gPlusShapeImage_eq_of_ramseyApprox_eq
    (family : List (NormalizedForbidden db du dd))
    (b q : Nat)
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (hApprox :
      SuccessorTree.SMTree.ramseyApprox
        (normalizedKptSMTree family) (b+1) F =
      SuccessorTree.SMTree.ramseyApprox
        (normalizedKptSMTree family) (b+1) G)
    (A : Fin q → FiniteGPlusVertex family)
    (hA : A ∈ boundedGPlusTuplePalette family b q) :
    (fun i => gPlusShapeImage F.map (A i)) =
      (fun i => gPlusShapeImage G.map (A i)) := by
  have hValue := congrArg Subtype.val hApprox
  have hAgree :
      ∀ x : AdmissibleKptNode family,
        LevelTree.lev x ≤ b → F.map x = G.map x := by
    intro x hx
    have hh :
        F.restrictLe (normalizedKptSMTree family) b =
        G.restrictLe (normalizedKptSMTree family) b := hValue
    exact congrFun hh ⟨x,hx⟩
  exact gPlusShapeImage_eq_of_agree_bounded_tuple
    family b q F.map G.map hAgree A hA

end SuccessorTree.V10
