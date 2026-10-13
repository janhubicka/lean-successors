import SuccessorTree.V10.M2SelectedCopyType
import SuccessorTree.V10.M2SelectedFamilyPadding
import Mathlib.Tactic

/-!
# Simultaneously realize all upper types from an M2 forbidden copy

The bounded real-coordinate source age has an honest initial L carrier,
all its dummy vertices are neutral, and the genuinely selected vertices
carry exactly their original source type by retained-record recovery.
The previously checked compatible-family padding theorem can therefore
realize all selected full L+ source types in one admissible partial
structure without assigning a prescribed type to any dummy vertex.
-/
namespace SuccessorTree.V10

/-- The target upper types pulled back along a genuine shape map can be
realized *simultaneously*, with all mutual L atoms preserved. The age
hypothesis is only forbidden avoidance of the target with its gap vertex
removed. Auxiliary E is introduced in the padded source witness rather
than on the target. -/
theorem boundedCopySourceAge_selected_family_padded
    {n m r db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (anchor : PartialTypeWithE n db du dd)
    (hAnchor : IsAdmissibleRawType family
      (⟨n,anchor⟩ : RawPartialTypeNode db du dd))
    (V : AgeTestModel db du dd) (e : Fin r → Nat)
    (hE : StrictMono e)
    (hBelow : ∀ i, i < n → kptShapeLevelMap family F i < m)
    (hLow : ∀ i, i < n → kptShapeLevelMap family F i ∈ V.carrier)
    (hUpper : ∀ a : Fin r, m < e a → e a ∈ V.carrier)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids V)
    (T : Fin r → PartialTypeWithE n db du dd)
    (hAd : ∀ a : Fin r, m < e a →
      IsAdmissibleRawType family
        (⟨n,T a⟩ : RawPartialTypeNode db du dd))
    (hComp : ∀ a : Fin r, m < e a → SameOrdinaryAtCut anchor (T a))
    (hInitial : ∀ (x y : Nat) (hx : x < n) (hy : y < n) (t : Fin db),
      V.binary (kptShapeLevelMap family F x)
        (kptShapeLevelMap family F y) t =
          anchor.lReduct.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t)
    (hImage : ∀ (a : Fin r) (ha : m < e a),
      let u : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
      RelationalPrefixType.ofAgeModel V (LevelTree.lev (F u)) (e a) =
        (F u).1.2.lReduct) :
    ∃ B : EnumeratedPartialStructure db du dd,
      (∀ bad, bad ∈ family → bad.Avoids B.L) ∧
      B.size = NonedgePadding.size n (n+r) ∧
      ∀ a : Fin r, ∀ ha : m < e a,
        B.partialTypeAt n (NonedgePadding.address n (n+a.val)) = T a := by
  classical
  let lambda := kptShapeLevelMap family F
  let A := boundedCopySourceAge V lambda n m r e
  have hAvoidA : ∀ bad, bad ∈ family → bad.Avoids A := by
    exact boundedCopySourceAge_avoids family V lambda n m r e
      (kptShapeLevelMap_strictMono family F) hE hBelow hLow hUpper hAvoid
  let selected (i : Nat) : Prop :=
    ∃ a : Fin r, i = n+a.val ∧ m < e a
  let types (i : Nat) : PartialTypeWithE n db du dd :=
    if h : i-n < r then T ⟨i-n,h⟩ else anchor
  have hTypes (a : Fin r) : types (n+a.val) = T a := by
    have hBound : n+a.val-n < r := by omega
    have hVal : n + a.val - n = a.val := by omega
    have hFin : (⟨n + a.val - n, hBound⟩ : Fin r) = a := Fin.ext hVal
    simpa only [types, dite_eq_left hBound, hFin]
  have hCarrier : ∀ x, x ∈ A.carrier ↔ x < n+r := by
    intro x
    rfl
  have hInitialA : ∀ (x y : Nat) (hx : x < n) (hy : y < n)
      (t : Fin db), A.binary x y t =
        anchor.lReduct.binary (some ⟨x,hx⟩) (some ⟨y,hy⟩) t := by
    intro x y hx hy t
    have hRealX : boundedCopyReal n m r e x := Or.inl hx
    have hRealY : boundedCopyReal n m r e y := Or.inl hy
    rw [boundedCopySourceAge_real_binary V lambda n m r e
      x y (by omega) (by omega) hRealX hRealY t]
    simp only [boundedCopyAddress_low lambda n r e x hx,
      boundedCopyAddress_low lambda n r e y hy]
    exact hInitial x y hx hy t
  have hAdSelected : ∀ i, n ≤ i → i < n+r → selected i →
      IsAdmissibleRawType family
        (⟨n,types i⟩ : RawPartialTypeNode db du dd) := by
    intro i _hi _hBound ⟨a,hi,ha⟩
    subst i
    simpa only [hTypes a] using hAd a ha
  have hCompSelected : ∀ i, n ≤ i → i < n+r → selected i →
      SameOrdinaryAtCut anchor (types i) := by
    intro i _hi _hBound ⟨a,hi,ha⟩
    subst i
    simpa only [hTypes a] using hComp a ha
  have hTypeSelected : ∀ i, n ≤ i → i < n+r → selected i →
      RelationalPrefixType.ofAgeModel A n i = (types i).lReduct := by
    intro i _hi _hBound ⟨a,hi,ha⟩
    subst i
    rw [hTypes a]
    let u : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
    have h := boundedCopySourceAge_selected_type_of_shapeMap
      family F u V m r e a ha (hImage a ha)
    change RelationalPrefixType.ofAgeModel A n (n+a.val) = (T a).lReduct at h
    exact h
  obtain ⟨B,hAvoidB,hSize,hSelected⟩ :=
    compatibleSelectedTypes_joint_padded family anchor hAnchor A (n+r)
      (by omega) hCarrier hAvoidA hInitialA selected types
      hAdSelected hCompSelected hTypeSelected
  refine ⟨B,hAvoidB,hSize,?_⟩
  intro a ha
  have hSel : selected (n+a.val) := ⟨a,rfl,ha⟩
  simpa only [hTypes a] using hSelected (n+a.val)
    (by omega) (by omega) hSel

end SuccessorTree.V10