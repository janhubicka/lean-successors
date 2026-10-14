import SuccessorTree.V10.M2SelectedCopyPadded
import SuccessorTree.V10.M2B3CopyCases
import SuccessorTree.V10.M2SourceTypeAge
import Mathlib.Tactic

/-!
# M2: the multi-upper B3 contradiction after selecting genuine source types

A forbidden copy whose upper vertices are labelled by compatible actual
level-n source types cannot occur in the target L-age witness after the
gap has been reinserted. The source of the contradiction is ONE
simultaneously padded admissible partial structure, not a fictitious
E-expansion of the target witness. The full L-reduct of its padding is
retained, including upper--upper nonedges and negative directed atoms.

The remaining M2 step is to *extract* such compatible source labels and
the initial lower record from arbitrary finite compatible B3 boundary
data. This theorem does not assume or prove B3 or M2.
-/

namespace SuccessorTree.V10

/-- Combine simultaneous nonedge padding, complete shape-map transport,
and induced-copy assembly into a contradiction for a selected multi-upper
forbidden pattern. All assumptions refer to genuine source labels,
the literal finite target L-age, and its forbidden-free gap deletion.
There is no hypothetical finite E expansion of the target. -/
theorem m2B3_selected_upper_forbidden_contradiction
    {n m r db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (W : AgeTestModel db du dd)
    (e : Fin r → Nat)
    (anchor : PartialTypeWithE n db du dd)
    (hAnchor : IsAdmissibleRawType family
      (⟨n,anchor⟩ : RawPartialTypeNode db du dd))
    (T : Fin r → PartialTypeWithE n db du dd)
    (hnPos : 0 < n)
    (hCut : kptShapeLevelMap family F n = m+1)
    (hBelow : ∀ i, i < n → kptShapeLevelMap family F i < m)
    (hCarrier : ∀ k, k ≤ m → k ∈ W.carrier)
    (hWithout : ∀ bad, bad ∈ family →
      bad.Avoids (W.withoutVertex m))
    (hAd : ∀ (a : Fin r), m < e a →
      IsAdmissibleRawType family
        (⟨n,T a⟩ : RawPartialTypeNode db du dd))
    (hComp : ∀ (a : Fin r), m < e a →
      SameOrdinaryAtCut anchor (T a))
    (hInitial : ∀ (x y : Nat) (hx : x < n) (hy : y < n)
      (t : Fin db),
      W.binary (kptShapeLevelMap family F x)
        (kptShapeLevelMap family F y) t =
          anchor.lReduct.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t)
    (hImage : ∀ (a : Fin r) (ha : m < e a),
      let t : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
      RelationalPrefixType.ofAgeModel W (LevelTree.lev (F t)) (e a) =
        (F t).1.2.lReduct)
    (P : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : P.Irreducible)
    (hMember : NormalizedForbidden.nontrivial r P hr hIrred ∈ family)
    (hCopy : W.Realizes P e)
    (hUpper : ∃ a : Fin r, m < e a) :
    False := by
  let lambda := kptShapeLevelMap family F
  have hLowInside :
      ∀ i, i < n → lambda i ∈ (W.withoutVertex m).carrier := by
    intro i hi
    change lambda i ∈ W.carrier ∧ lambda i ≠ m
    have hSmall : lambda i < m := hBelow i hi
    exact ⟨hCarrier (lambda i) (Nat.le_of_lt hSmall),
      Nat.ne_of_lt hSmall⟩
  have hUpperInside :
      ∀ a : Fin r, m < e a → e a ∈ (W.withoutVertex m).carrier := by
    intro a ha
    change e a ∈ W.carrier ∧ e a ≠ m
    exact ⟨hCopy.2.1 a, by omega⟩
  have hInitialWithout :
      ∀ (x y : Nat) (hx : x < n) (hy : y < n)
        (t : Fin db),
      (W.withoutVertex m).binary (lambda x) (lambda y) t =
        anchor.lReduct.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t := by
    intro x y hx hy t
    change W.binary (lambda x) (lambda y) t = _
    exact hInitial x y hx hy t
  have hImageWithout : ∀ (a : Fin r) (ha : m < e a),
      let t : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
      RelationalPrefixType.ofAgeModel (W.withoutVertex m)
        (LevelTree.lev (F t)) (e a) =
          (F t).1.2.lReduct := by
    intro a ha
    change RelationalPrefixType.ofAgeModel W
      (LevelTree.lev (F (⟨⟨n,T a⟩,hAd a ha⟩ :
          AdmissibleKptNode family))) (e a) =
        (F (⟨⟨n,T a⟩,hAd a ha⟩ :
          AdmissibleKptNode family)).1.2.lReduct
    exact hImage a ha
  obtain ⟨B,hAvoidB,hSize,hL,hSelected⟩ :=
    boundedCopySourceAge_selected_family_padded_with_L
      family F anchor hAnchor (W.withoutVertex m) e hCopy.1
      hBelow hLowInside hUpperInside hWithout T hAd hComp
      hInitialWithout hImageWithout
  let u := NonedgePadding.socleCapNode family B hAvoidB
  have hImageCopy : (F u).1.2.ageModel.Realizes P
      (m2ForbiddenCopyImage lambda n m r e) :=
    m2ForbiddenCopy_from_padded_cap_of_upper
      family F W e B hAvoidB hSize hL T hnPos hAd hSelected
      hImage hCut hCarrier hUpper P hCopy
  have hAvoidImage : ∀ bad, bad ∈ family →
      bad.Avoids (F u).1.2.ageModel :=
    PartialTypeWithE.ageModel_avoids family (F u).1.2 (F u).2
  exact (hAvoidImage (.nontrivial r P hr hIrred) hMember)
    ⟨_, hImageCopy⟩

end SuccessorTree.V10
