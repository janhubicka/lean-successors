import SuccessorTree.V10.M2CapPaddedRecords
import SuccessorTree.V10.M2SelectedCapTransport
import SuccessorTree.V10.M2CopyFromCompleteImageTypes
import Mathlib.Tactic

/-!
# Complete induced copies from one actual padded source and one cap image

The complete source types of selected real upper vertices are realized
inside one padded witness. Canonical parameter transport identifies
their *entire* target types, including the omitted gap coordinate.
Full retained record transport identifies upper--upper atoms. Given
the common initial target socle, the finite induced-copy assembly is
then unconditional and works for all directed positive and negative
atoms, loops, unary predicates and diagonal predicates.
-/
namespace SuccessorTree.V10

/-- The final image-copy lemma for a genuinely padded source. It is
independent of the B3 age test; the remaining B3 construction must
supply this witness and initial socle from its actual boundary data. -/
theorem m2ForbiddenCopy_from_padded_cap
    {n m r db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (W : AgeTestModel db du dd) (e : Fin r → Nat)
    (B : EnumeratedPartialStructure db du dd)
    (hAvoidB : ∀ bad, bad ∈ family → bad.Avoids B.L)
    (hSize : B.size = NonedgePadding.size n (n+r))
    (hL : B.L = NonedgePadding.model
      (boundedCopySourceAge (W.withoutVertex m)
        (kptShapeLevelMap family F) n m r e) n (n+r))
    (T : Fin r → PartialTypeWithE n db du dd)
    (hnPos : 0 < n)
    (hAd : ∀ (a : Fin r), m < e a →
      IsAdmissibleRawType family
        (⟨n,T a⟩ : RawPartialTypeNode db du dd))
    (hSelected : ∀ (a : Fin r) (_ha : m < e a),
      B.partialTypeAt n (NonedgePadding.address n (n+a.val)) = T a)
    (hImage : ∀ (a : Fin r) (ha : m < e a),
      let t : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
      RelationalPrefixType.ofAgeModel W (LevelTree.lev (F t)) (e a) =
        (F t).1.2.lReduct)
    (hCut : kptShapeLevelMap family F n = m+1)
    (hInitial : SameInitialL
      (F (NonedgePadding.socleCapNode family B hAvoidB)).1.2.ageModel W m)
    (P : ForbiddenAtomicPattern r db du dd)
    (hCopy : W.Realizes P e) :
    (F (NonedgePadding.socleCapNode family B hAvoidB)).1.2.ageModel.Realizes P
      (m2ForbiddenCopyImage (kptShapeLevelMap family F) n m r e) := by
  let lambda := kptShapeLevelMap family F
  let u := NonedgePadding.socleCapNode family B hAvoidB
  have hMono : StrictMono lambda := kptShapeLevelMap_strictMono family F
  have hGap : m < lambda n := by dsimp [lambda]; rw [hCut]; omega
  have hUpper : ∀ (a : Fin r) (ha : m < e a),
      ∃ (hj : lambda (NonedgePadding.address n (n+a.val)) < LevelTree.lev (F u))
        (hq : m+1 ≤ LevelTree.lev (F u)),
        ((F u).1.2.ordinaryType
          (lambda (NonedgePadding.address n (n+a.val))) hj (m+1) hq).lReduct =
            RelationalPrefixType.ofAgeModel W (m+1) (e a) := by
    intro a ha
    let t : AdmissibleKptNode family := ⟨⟨n,T a⟩,hAd a ha⟩
    let j := NonedgePadding.address n (n+a.val)
    have hjB : j < B.size := by
      rw [hSize]
      exact NonedgePadding.address_lt_size n (n+r) (n+a.val) (by omega)
    have hnj : n ≤ j := by
      simp [j,NonedgePadding.address]
      omega
    obtain ⟨hj,hq,hType⟩ :=
      shapeMap_transports_padded_selected_type family F B hAvoidB
        j hnPos hnj hjB (T a) (hAd a ha) (hSelected a ha)
    have hLevel : LevelTree.lev (F t) = m+1 := by
      calc
        LevelTree.lev (F t) = lambda n := by
          exact (kptShapeLevelMap_eq family F t).symm
        _ = m+1 := hCut
    have hq' : m+1 ≤ LevelTree.lev (F u) := by
      rw [←hLevel]
      exact hq
    refine ⟨hj,hq',?_⟩
    have hSource :
        ((F u).1.2.ordinaryType (lambda j) hj (LevelTree.lev (F t)) hq).lReduct =
          RelationalPrefixType.ofAgeModel W (LevelTree.lev (F t)) (e a) := by
      exact (congrArg PartialTypeWithE.lReduct hType).trans (hImage a ha).symm
    have hSourceAll :
        ∀ (h : (LevelTree.lev (F t)) ≤ LevelTree.lev (F u)),
          ((F u).1.2.ordinaryType (lambda j) hj (LevelTree.lev (F t)) h).lReduct =
            RelationalPrefixType.ofAgeModel W (LevelTree.lev (F t)) (e a) := by
      intro h
      have heq : h = hq := Subsingleton.elim _ _
      subst h
      exact hSource
    have hNewAll :
        ∀ (h : m+1 ≤ LevelTree.lev (F u)),
          ((F u).1.2.ordinaryType (lambda j) hj (m+1) h).lReduct =
            RelationalPrefixType.ofAgeModel W (m+1) (e a) := by
      exact hLevel ▸ hSourceAll
    simpa only [j] using hNewAll hq'
  have hHighHigh : ∀ (a b : Fin r), m < e a → m < e b →
      ∀ t : Fin db,
        (F u).1.2.ageModel.binary
          (lambda (NonedgePadding.address n (n+a.val)))
          (lambda (NonedgePadding.address n (n+b.val))) t =
            W.binary (e a) (e b) t := by
    intro a b ha hb t
    obtain ⟨_,_,hRecord⟩ := shapeMap_boundedCopy_cap_upper_pair
      family F (W.withoutVertex m) e B hAvoidB hSize hL a b ha hb t
    exact hRecord
  exact m2ForbiddenCopy_from_complete_upper_types
    (F u).1.2 W lambda n m e hMono hGap hInitial
      hUpper hHighHigh P hCopy

end SuccessorTree.V10
