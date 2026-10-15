import SuccessorTree.V10.KptE1ShapeLevelCut
import SuccessorTree.V10.CanonicalStepGraph
import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# Recover the genuine target canonical E cut from image parameters

The missing Kpt E1 step must not prescribe an arbitrary target
new-ordinary E cut. A defined target successor is canonical, and
its actual parameter list is the image of the source list under
the genuine shape map. Since the Kpt canonical parameter is either
empty (cut zero) or a positive singleton (at exactly its free cut),
the target cut is determined by the image of the source parameter.

The results below prove this directly for the genuine admissible
Kpt S-tree. They reuse the canonical successor graph and the
previously verified strictly increasing Kpt shape level map.
There is NO assumption of E1 or of a new partial-structure witness.
The further step is to identify the complete retained predecessor
and source letter, and use the padded admissibility construction.
-/

namespace SuccessorTree.V10

/-- The canonical parameter list is empty exactly when the true
new-ordinary E cut is zero, even when the list was obtained by
mapping genuine Kpt source nodes. -/
theorem kptImageParameter_empty_iff_cut_zero
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {ell : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (g : Nat) (hg : g ≤ ell)
    (p : List (AdmissibleKptNode family))
    (hParam : ((p.map F).map (fun x => x.1)) =
      (Q.canonicalParameterRecord g hg).toList) :
    p = [] ↔ g = 0 := by
  constructor
  · intro hp
    subst p
    by_contra hZero
    simp [PartialTypeWithE.canonicalParameterRecord, hZero] at hParam
  · intro hZero
    have hLen := congrArg List.length hParam
    have hpLen : p.length = 0 := by
      simpa [PartialTypeWithE.canonicalParameterRecord, hZero] using hLen
    cases p with
    | nil => rfl
    | cons x xs => simp at hpLen

/-- If one genuine source parameter maps to the target's canonical
nonempty parameter list, the target's E cut is LITERALLY the
shape-level image of the source parameter's level. -/
theorem kptImageParameter_singleton_cut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {ell : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (g : Nat) (hg : g ≤ ell)
    (x : AdmissibleKptNode family)
    (hParam : (([x].map F).map (fun y => y.1)) =
      (Q.canonicalParameterRecord g hg).toList) :
    kptShapeLevelMap family F (LevelTree.lev x) = g := by
  have hNonzero : g ≠ 0 := by
    intro hz
    simp [PartialTypeWithE.canonicalParameterRecord, hz] at hParam
  have hRaw :
      (F x).1 =
        (⟨g,Q.lastOrdinaryParameter g hg⟩ :
          RawPartialTypeNode db du dd) := by
    simpa [PartialTypeWithE.canonicalParameterRecord, hNonzero] using hParam
  rw [kptShapeLevelMap_eq family F x]
  exact congrArg Sigma.fst hRaw

/-- Root preservation forces every *source* parameter in a
nonempty genuine image-parameter record to lie at a positive level.
This is not obtained by introducing a new positivity axiom. -/
theorem kptImageParameter_singleton_source_positive
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hF : F ∈ KptM family)
    {ell : Nat}
    (Q : PartialTypeWithE (ell + 1) db du dd)
    (g : Nat) (hg : g ≤ ell)
    (x : AdmissibleKptNode family)
    (hParam : (([x].map F).map (fun y => y.1)) =
      (Q.canonicalParameterRecord g hg).toList) :
    0 < LevelTree.lev x := by
  have hgPos : 0 < g := by
    by_contra h
    have hz : g = 0 := by omega
    simp [PartialTypeWithE.canonicalParameterRecord, hz] at hParam
  have hLevel :=
    kptImageParameter_singleton_cut family F Q g hg x hParam
  rw [kptShapeLevelMap_eq family F x] at hLevel
  by_contra hPos
  have hx0 : LevelTree.lev x = 0 := by omega
  have hTarget0 : LevelTree.lev (F x) = 0 := hF x hx0
  omega

/-- The target of a REAL defined Kpt successor exposes the exact
canonical E cut, predecessor and terminal letter, and the complete
image-parameter dichotomy. No abstract or assumed successor appears. -/
theorem actualKptTargetStep_imageParameterCut
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (a b : AdmissibleKptNode family)
    (p : List (AdmissibleKptNode family))
    (c : AdmissibleKptSigma family)
    (hStep :
      (admissibleKptSTree family).succ (F a) (p.map F) c = some b) :
    ∃ (ell g : Nat) (hg : g ≤ ell)
      (Q : PartialTypeWithE (ell + 1) db du dd),
      (F a).1 =
        (⟨ell,Q.restrict (Nat.le_succ ell)⟩ :
          RawPartialTypeNode db du dd) ∧
      b.1 = (⟨ell+1,Q⟩ : RawPartialTypeNode db du dd) ∧
      c.1 = Q.terminalLetter ∧
      ValidNewOrdinaryColumn Q g ∧
      (p = [] ↔ g = 0) ∧
      (∀ x : AdmissibleKptNode family, p = [x] →
        g = kptShapeLevelMap family F (LevelTree.lev x)) ∧
      (g = 0 ∨ g < ell) := by
  have hRaw :
      canonicalKptSucc family (F a) (p.map F) c.1 = some b := by
    simpa only [admissibleKptSTree_succ_eq] using hStep
  obtain ⟨ell,g,hg,Q,hBase,hTarget,hLetter,hValid,hParam,hGate⟩ :=
    canonicalKptSucc_spec family hRaw
  refine ⟨ell,g,hg,Q,hBase,hTarget,hLetter,hValid,?_,?_,hGate⟩
  · exact kptImageParameter_empty_iff_cut_zero
      family F Q g hg p hParam
  · intro x hx
    subst p
    exact (kptImageParameter_singleton_cut
      family F Q g hg x hParam).symm

end SuccessorTree.V10
