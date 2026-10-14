import SuccessorTree.V10.LocalAgeNeutralUpperSucc
import SuccessorTree.V10.ConcreteKptM1
import Mathlib.Tactic

/-!
# A genuine shape-preserving Kpt one-gap map from neutral insertion

This is the first complete global shape map in the normalized finite
unary/binary admissible Kpt S-tree constructed without postulating a map.
It inserts a neutral ordinary coordinate ell>0 uniformly into EVERY
admissible Kpt type.

The predecessor modules prove:
* total admissibility and unique image independent of ambient witnesses;
* injectivity on Kpt nodes, not just original vertex addresses;
* strictly increasing level map, fixing all roots;
* all complete L+ prefix relations, including across the gap;
* weak successor preservation below ell (the old successor appears as a
  prefix of the shifted target), and exact successor preservation above.

Thus the assembled ShapeMap belongs to the manuscript's concrete monoid
KptM (maps fixing level zero) and omits the desired target level ell.

The stronger property SkipsOnly ell needs a separate proof that the
admissible Kpt tree has a node at every unskipped level. This module
does NOT supply the prescribed NON-neutral crossing map of Lemma 6.51,
nor the global M2/M3 axioms.
-/

namespace SuccessorTree.V10

/-- The genuine weak successor property for the total neutral gap map,
with the actual admissible Sigma alphabet and mapped parameter list. -/
theorem neutralKptSkip_weak_succ
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell)
    {a b : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)}
    {c : AdmissibleKptSigma family}
    (h : (admissibleKptSTree family).succ a p c = some b) :
    ∃ d : AdmissibleKptNode family,
      (admissibleKptSTree family).succ
        (neutralKptSkip family ell hellPos a)
        (p.map (neutralKptSkip family ell hellPos)) c = some d ∧
      d ≤ neutralKptSkip family ell hellPos b := by
  by_cases haLow : a.1.1 < ell
  · exact neutralKptSkip_weak_succ_below_gap family ell hellPos
      h haLow
  · have haHigh : ell ≤ a.1.1 := by omega
    exact ⟨neutralKptSkip family ell hellPos b,
      neutralKptSkip_weak_succ_above_gap family ell hellPos h haHigh,
      le_rfl⟩

/-- The uniform neutral Kpt insertion is a full concrete ShapeMap, not
merely an order-preserving map with a chosen level injection. -/
noncomputable def neutralKptShapeMap
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell) :
    SuccessorTree.ShapeMap (admissibleKptSTree family) where
  toFun := neutralKptSkip family ell hellPos
  injective' := neutralKptSkip_injective family ell hellPos
  level_preserving' := by
    intro a b h
    exact neutralKptSkip_preserves_equal_level family ell hellPos a b h
  weak_succ' := by
    intro a b p c h
    exact neutralKptSkip_weak_succ family ell hellPos h
  root_le' := by
    intro a ha
    have hLow : a.1.1 < ell := by
      change a.1.1 = 0 at ha
      omega
    change a ≤ neutralKptSkip family ell hellPos a
    rw [neutralKptSkip_fixed_below family ell hellPos a hLow]

/-- The concrete map fixes roots, hence belongs to the precise monoid
chosen in Section 6.3. -/
theorem neutralKptShapeMap_mem_KptM
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell) :
    neutralKptShapeMap family ell hellPos ∈ KptM family := by
  intro a ha
  change (neutralKptSkip family ell hellPos a).1.1 = 0
  have hLow : a.1.1 < ell := by
    change a.1.1 = 0 at ha
    omega
  rw [neutralKptSkip_fixed_below family ell hellPos a hLow]
  exact ha

/-- The inserted level is absent from the entire range of the actual
shape-preserving map, not just from a finite-model example. -/
theorem neutralKptShapeMap_skips
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (ell : Nat) (hellPos : 0 < ell) :
    (neutralKptShapeMap family ell hellPos).Skips ell := by
  intro h
  obtain ⟨a, ha⟩ := h
  exact neutralKptSkip_omits_level family ell hellPos a ha

end SuccessorTree.V10
