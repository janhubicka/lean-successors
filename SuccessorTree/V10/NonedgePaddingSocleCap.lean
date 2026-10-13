import SuccessorTree.V10.NonedgePaddingFullTypes
import SuccessorTree.V10.AdmissibleKptLevelTree
import SuccessorTree.V10.PrefixReplicaE
import Mathlib.Tactic

/-!
# A genuine Kpt type above the entire padded source witness

Non-edge padding realizes the prescribed upper partial types in one
finite partial structure. To apply an arbitrary ShapeMap to that same
witness, we need a SINGLE admissible type whose ordinary socle contains
all its vertices. Add two neutral vertices, putting the final
distinguished vertex at size+1 and its free E cut at the original size.

All old L atoms and the full old E record are retained. The intermediate
position is L-isolated, and the distinguished vertex has no L edges.
Irreducibility of the normalized forbidden patterns preserves the age.
No M2, B3, or arbitrary age-preservation assumption on the ShapeMap.
-/

namespace SuccessorTree.V10
namespace NonedgePadding

/-- Append two L-neutral positions. The nested existing padding
constructor supplies the forbidden-age theorem twice. -/
def twoNeutralL {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) : AgeTestModel db du dd :=
  model (model A.L A.size A.size) (A.size+1) (A.size+1)

/-- At coordinates below the copied initial segment, the non-edge
padding constructor preserves every directed positive and negative atom. -/
theorem model_old_binary {db du dd : Nat}
    (L : AgeTestModel db du dd) (n N x y : Nat)
    (hx : x < n) (hy : y < n) (t : Fin db) :
    (model L n N).binary x y t = L.binary x y t := by
  have hrx : Real n x := Or.inl hx
  have hry : Real n y := Or.inl hy
  simp [model,hrx,hry,project,hx,hy]

theorem model_old_unary {db du dd : Nat}
    (L : AgeTestModel db du dd) (n N x : Nat)
    (hx : x < n) (t : Fin du) :
    (model L n N).unary x t = L.unary x t := by
  have hrx : Real n x := Or.inl hx
  simp [model,hrx,project,hx]

theorem model_old_diagonal {db du dd : Nat}
    (L : AgeTestModel db du dd) (n N x : Nat)
    (hx : x < n) (t : Fin dd) :
    (model L n N).diagonal x t = L.diagonal x t := by
  have hrx : Real n x := Or.inl hx
  simp [model,hrx,project,hx]

/-- A non-real padding vertex has no incident L relation, in either
direction, regardless of the other vertex. -/
theorem model_neutral_left {db du dd : Nat}
    (L : AgeTestModel db du dd) (n N x y : Nat)
    (hx : ¬ Real n x) (t : Fin db) :
    (model L n N).binary x y t = false := by
  simp [model,hx]

theorem model_neutral_right {db du dd : Nat}
    (L : AgeTestModel db du dd) (n N x y : Nat)
    (hy : ¬ Real n y) (t : Fin db) :
    (model L n N).binary x y t = false := by
  simp [model,hy]

/-- The two padding steps are literal identity on the original
carrier, even for absent atoms. -/
theorem twoNeutralL_old_binary {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (x y : Nat) (hx : x < A.size) (hy : y < A.size)
    (t : Fin db) :
    (twoNeutralL A).binary x y t = A.L.binary x y t := by
  calc
    (twoNeutralL A).binary x y t =
      (model A.L A.size A.size).binary x y t :=
        model_old_binary (model A.L A.size A.size)
          (A.size+1) (A.size+1) x y (by omega) (by omega) t
    _ = A.L.binary x y t :=
        model_old_binary A.L A.size A.size x y hx hy t

theorem twoNeutralL_old_unary {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (x : Nat) (hx : x < A.size) (t : Fin du) :
    (twoNeutralL A).unary x t = A.L.unary x t := by
  calc
    (twoNeutralL A).unary x t =
      (model A.L A.size A.size).unary x t :=
        model_old_unary (model A.L A.size A.size)
          (A.size+1) (A.size+1) x (by omega) t
    _ = A.L.unary x t := model_old_unary A.L A.size A.size x hx t

theorem twoNeutralL_old_diagonal {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (x : Nat) (hx : x < A.size) (t : Fin dd) :
    (twoNeutralL A).diagonal x t = A.L.diagonal x t := by
  calc
    (twoNeutralL A).diagonal x t =
      (model A.L A.size A.size).diagonal x t :=
        model_old_diagonal (model A.L A.size A.size)
          (A.size+1) (A.size+1) x (by omega) t
    _ = A.L.diagonal x t :=
        model_old_diagonal A.L A.size A.size x hx t

/-- No L relation involves the two fresh vertices. -/
theorem twoNeutralL_binary_new {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (x y : Nat) (hx : x < A.size+2) (hy : y < A.size+2)
    (hNew : A.size ≤ x ∨ A.size ≤ y) (t : Fin db) :
    (twoNeutralL A).binary x y t = false := by
  rcases hNew with hNew | hNew
  · have hxCases : x = A.size ∨ x = A.size+1 := by omega
    rcases hxCases with rfl | rfl
    · calc
        (twoNeutralL A).binary A.size y t =
            (model A.L A.size A.size).binary A.size y t :=
              model_old_binary (model A.L A.size A.size)
                (A.size+1) (A.size+1) A.size y (by omega) (by omega) t
        _ = false :=
          model_neutral_left A.L A.size A.size A.size y (by simp [Real]) t
    · exact model_neutral_left (model A.L A.size A.size)
        (A.size+1) (A.size+1) (A.size+1) y (by simp [Real]) t
  · have hyCases : y = A.size ∨ y = A.size+1 := by omega
    rcases hyCases with rfl | rfl
    · calc
        (twoNeutralL A).binary x A.size t =
            (model A.L A.size A.size).binary x A.size t :=
              model_old_binary (model A.L A.size A.size)
                (A.size+1) (A.size+1) x A.size (by omega) (by omega) t
        _ = false :=
          model_neutral_right A.L A.size A.size x A.size (by simp [Real]) t
    · exact model_neutral_right (model A.L A.size A.size)
        (A.size+1) (A.size+1) x (A.size+1) (by simp [Real]) t

/-- Two neutral fillers followed by the canonical maximal incoming E
socle: the last vertex has precisely the original free cut. -/
def socleCap {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) :
    EnumeratedPartialStructure db du dd where
  size := A.size+2
  L := twoNeutralL A
  carrier_iff := by
    intro x
    change x < size (A.size+1) (A.size+1) ↔ x < A.size+2
    simp [size]
    omega
  E := prefixReplicaE A A.size
  E_inside := by
    intro u v h
    by_cases hv : v < A.size
    · have hOld : A.E u v = true := by
        simpa [prefixReplicaE,hv] using h
      have hIn := A.E_inside u v hOld
      exact ⟨by omega,by omega⟩
    · by_cases hLast : v = A.size+1
      · have hu : u < A.size := by
          simpa [prefixReplicaE,hv,hLast] using h
        exact ⟨by omega,by omega⟩
      · simp [prefixReplicaE,hv,hLast] at h
  spaced := prefixReplicaE_spaced A A.size
  downward := prefixReplicaE_downward A A.size
  linked_E := by
    intro u v huv hu hv hLink
    by_cases hOld : v < A.size
    · have huOld : u < A.size := by omega
      have hLinkOld : ∃ t : Fin db,
          A.L.binary u v t = true ∨ A.L.binary v u t = true := by
        rcases hLink with ⟨t,ht | ht⟩
        · exact ⟨t,Or.inl
            ((twoNeutralL_old_binary A u v huOld hOld t).symm.trans ht)⟩
        · exact ⟨t,Or.inr
            ((twoNeutralL_old_binary A v u hOld huOld t).symm.trans ht)⟩
      exact (prefixReplicaE_old A A.size u v hOld).trans
        (A.linked_E u v huv huOld hOld hLinkOld)
    · rcases hLink with ⟨t,ht | ht⟩
      · have h0 := twoNeutralL_binary_new A u v hu hv
          (Or.inr (by omega)) t
        simp [h0] at ht
      · have h0 := twoNeutralL_binary_new A v u hv hu
          (Or.inl (by omega)) t
        simp [h0] at ht

theorem socleCap_old_E {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) (hv : v < A.size) :
    (socleCap A).E u v = A.E u v :=
  prefixReplicaE_old A A.size u v hv

/-- Keeping each old E-column unchanged also keeps its canonically
determined free cut; this is needed to identify the genuine
successor parameter of an ordinary source vertex. -/
theorem socleCap_old_freeLevel {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (j : Nat) (hj : j < A.size) :
    (socleCap A).freeLevel j = A.freeLevel j := by
  apply Nat.le_antisymm
  · by_contra hNot
    have h : A.freeLevel j < (socleCap A).freeLevel j := by omega
    have hE : (socleCap A).E (A.freeLevel j) j = true :=
      ((socleCap A).E_iff_freeLevel (A.freeLevel j) j).2 h
    have hOld : A.E (A.freeLevel j) j = true :=
      (socleCap_old_E A (A.freeLevel j) j hj).symm.trans hE
    have hNot : A.E (A.freeLevel j) j ≠ true := by
      simp [A.freeLevel_firstMissing j]
    exact hNot hOld
  · by_contra hNot
    have h : (socleCap A).freeLevel j < A.freeLevel j := by omega
    have hE : A.E ((socleCap A).freeLevel j) j = true :=
      (A.E_iff_freeLevel ((socleCap A).freeLevel j) j).2 h
    have hNew : (socleCap A).E ((socleCap A).freeLevel j) j = true :=
      (socleCap_old_E A ((socleCap A).freeLevel j) j hj).trans hE
    have hNot : (socleCap A).E ((socleCap A).freeLevel j) j ≠ true := by
      simp [(socleCap A).freeLevel_firstMissing j]
    exact hNot hNew

/-- Every old ordinary vertex retains its COMPLETE type over each
original initial socle, including all directed, unary, diagonal and E
atoms; this is more precise than mere age preservation. -/
theorem socleCap_partialTypeAt {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (n j : Nat) (hn : n ≤ j) (hj : j < A.size) :
    (socleCap A).partialTypeAt n j = A.partialTypeAt n j := by
  have hIndex (x : Option (Fin n)) :
      prefixVertexIndex j x < A.size := by
    cases x with
    | none => exact hj
    | some i =>
        change i.val < A.size
        omega
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      change (twoNeutralL A).binary
          (prefixVertexIndex j x) (prefixVertexIndex j y) t =
        A.L.binary (prefixVertexIndex j x) (prefixVertexIndex j y) t
      exact twoNeutralL_old_binary A _ _ (hIndex x) (hIndex y) t
    · intro x t
      change (twoNeutralL A).unary (prefixVertexIndex j x) t =
        A.L.unary (prefixVertexIndex j x) t
      exact twoNeutralL_old_unary A _ (hIndex x) t
    · intro x t
      change (twoNeutralL A).diagonal (prefixVertexIndex j x) t =
        A.L.diagonal (prefixVertexIndex j x) t
      exact twoNeutralL_old_diagonal A _ (hIndex x) t
  · intro x y
    change (socleCap A).E (prefixVertexIndex j x)
        (prefixVertexIndex j y) =
      A.E (prefixVertexIndex j x) (prefixVertexIndex j y)
    exact socleCap_old_E A _ _ (hIndex y)

/-- Both rounds of non-edge padding preserve the normalized
forbidden-free age, including the allowed-neutral singleton case. -/
theorem socleCap_avoids {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    ∀ bad, bad ∈ family → bad.Avoids (socleCap A).L := by
  intro bad hbad
  have hFirst : bad.Avoids (model A.L A.size A.size) :=
    preserves_avoidance A.L A.size A.size le_rfl A.carrier_iff
      bad (hAvoid bad hbad)
  change bad.Avoids (twoNeutralL A)
  exact preserves_avoidance (model A.L A.size A.size)
    (A.size+1) (A.size+1) le_rfl
    (by
      intro x
      change x < size A.size A.size ↔ x < A.size+1
      simp [size])
    bad hFirst

/-- The cap has a free E socle containing ALL original positions,
not just the prescribed short cut. -/
theorem socleCap_freeLevel {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd) :
    (socleCap A).freeLevel (A.size+1) = A.size := by
  exact prefixReplicaE_last_freeLevel A A.size

/-- One genuine admissible type above every vertex of A.
This is the missing container for simultaneous transport by F. -/
noncomputable def socleCapNode {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (A : EnumeratedPartialStructure db du dd)
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L) :
    AdmissibleKptNode family := by
  let B := socleCap A
  have hAd : IsAdmissibleRawType family
      (⟨A.size,B.partialTypeAt A.size (A.size+1)⟩ :
        RawPartialTypeNode db du dd) := by
    refine ⟨B,A.size+1,?_,socleCap_avoids family A hAvoid,?_⟩
    · change A.size+1 < A.size+2
      omega
    · change (⟨A.size,B.partialTypeAt A.size (A.size+1)⟩ :
          RawPartialTypeNode db du dd) =
        (⟨B.freeLevel (A.size+1),
          B.partialTypeAt (B.freeLevel (A.size+1)) (A.size+1)⟩ :
          RawPartialTypeNode db du dd)
      rw [socleCap_freeLevel A]
  exact ⟨⟨A.size,B.partialTypeAt A.size (A.size+1)⟩,hAd⟩

end NonedgePadding
end SuccessorTree.V10
