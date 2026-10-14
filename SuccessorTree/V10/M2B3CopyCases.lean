import SuccessorTree.V10.M2ConcreteCapImageCopy
import SuccessorTree.V10.M2InitialSocleFromUpper
import Mathlib.Tactic

/-!
# The two cases in the M2 B3 forbidden-copy argument

A forbidden copy using only the common initial socle already contradicts
avoidance of the prescribed lower type. If there is an upper vertex,
the complete image of its genuine padded source type identifies the
initial socle automatically; there is no independent comparison hypothesis.

These lemmas do not assert that arbitrary B3 boundary data admit a
padded witness. Constructing that witness is the remaining global M2 step.
-/

namespace SuccessorTree.V10

/-- An induced forbidden pattern supported entirely by the common
initial socle transfers in either direction, including absent edges,
unary predicates and diagonal predicates. -/
theorem sameInitialL_realizes_below
    {r db du dd : Nat}
    (W D : AgeTestModel db du dd) (m : Nat)
    (P : ForbiddenAtomicPattern r db du dd) (e : Fin r → Nat)
    (hSame : SameInitialL W D m)
    (hBelow : ∀ a : Fin r, e a ≤ m)
    (hCopy : W.Realizes P e) :
    D.Realizes P e := by
  refine ⟨hCopy.1, ?_, ?_, ?_, ?_⟩
  · intro a
    exact (hSame.1 (e a) (hBelow a)).mp (hCopy.2.1 a)
  · intro a b hab t
    exact (hSame.2.1 (e a) (e b) (hBelow a) (hBelow b) t).symm.trans
      (hCopy.2.2.1 a b hab t)
  · intro a t
    exact (hSame.2.2.1 (e a) (hBelow a) t).symm.trans
      (hCopy.2.2.2.1 a t)
  · intro a t
    exact (hSame.2.2.2 (e a) (hBelow a) t).symm.trans
      (hCopy.2.2.2.2 a t)

/-- Once the common lower socle avoids a forbidden pattern, every
forbidden copy in a matching finite witness uses an upper vertex.
This is the entire zero-upper branch of the B3 contradiction. -/
theorem forbiddenCopy_has_upper_of_sameInitialL
    {r db du dd : Nat}
    (W D : AgeTestModel db du dd) (m : Nat)
    (P : ForbiddenAtomicPattern r db du dd) (e : Fin r → Nat)
    (hSame : SameInitialL W D m)
    (hAvoidD : ¬ ∃ f : Fin r → Nat, D.Realizes P f)
    (hCopy : W.Realizes P e) :
    ∃ a : Fin r, m < e a := by
  by_contra hNone
  have hBelow : ∀ a : Fin r, e a ≤ m := by
    intro a
    by_contra ha
    exact hNone ⟨a, by omega⟩
  exact hAvoidD ⟨e, sameInitialL_realizes_below
    W D m P e hSame hBelow hCopy⟩

/-- From ONE selected upper copy vertex in a genuine nonedge-padded
source, the transported full image type identifies the target's
entire initial L socle, including the gap coordinate m. In
particular, the separate hInitial hypothesis of
m2ForbiddenCopy_from_padded_cap is redundant in this case. -/
theorem m2ForbiddenCopy_from_padded_cap_of_upper
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
    (hCarrier : ∀ k, k ≤ m → k ∈ W.carrier)
    (hExists : ∃ a : Fin r, m < e a)
    (P : ForbiddenAtomicPattern r db du dd)
    (hCopy : W.Realizes P e) :
    (F (NonedgePadding.socleCapNode family B hAvoidB)).1.2.ageModel.Realizes P
      (m2ForbiddenCopyImage (kptShapeLevelMap family F) n m r e) := by
  obtain ⟨a,ha⟩ := hExists
  let u := NonedgePadding.socleCapNode family B hAvoidB
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
      LevelTree.lev (F t) = kptShapeLevelMap family F n :=
        (kptShapeLevelMap_eq family F t).symm
      _ = m+1 := hCut
  have hq' : m+1 ≤ LevelTree.lev (F u) := by
    rw [←hLevel]
    exact hq
  have hSource :
      ((F u).1.2.ordinaryType
        (kptShapeLevelMap family F j) hj (LevelTree.lev (F t)) hq).lReduct =
          RelationalPrefixType.ofAgeModel W (LevelTree.lev (F t)) (e a) :=
    (congrArg PartialTypeWithE.lReduct hType).trans (hImage a ha).symm
  have hTypeW :
      ((F u).1.2.ordinaryType
        (kptShapeLevelMap family F j) hj (m+1) hq').lReduct =
          RelationalPrefixType.ofAgeModel W (m+1) (e a) := by
    simpa only [hLevel] using hSource
  have hInitial : SameInitialL (F u).1.2.ageModel W m :=
    sameInitialL_of_complete_upper_type (F u).1.2 W m
      (kptShapeLevelMap family F j) (e a) hj hq'
      hCarrier hTypeW
  exact m2ForbiddenCopy_from_padded_cap
    family F W e B hAvoidB hSize hL T hnPos hAd hSelected hImage
    hCut hInitial P hCopy

end SuccessorTree.V10
