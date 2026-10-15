import SuccessorTree.V10.FiniteLayerEnumeration
import SuccessorTree.V10.CountableGPlusEmbedding

/-!
# An exhaustive size-nondecreasing enumeration of the genuine G+ vertices

Finite raw tables at one size form a finite type. The actual valid G+
vertices of that size form a subtype, hence are also finite. The prefix
map of any countable forbidden-free partial structure supplies a vertex
in every positive-size layer. We enumerate the layers by their finite
cardinalities and concatenate them using the proved cumulative rank.

The result is a genuine equivalence Nat ≃ G+, with nondecreasing sizes.
Neither an exhaustive enumeration nor its size property is assumed.
-/

namespace SuccessorTree.V10.GPlusEnumeration

variable {db du dd : Nat}

/-- At a fixed size, a code contains exactly its four finite atomic tables. -/
def fixedSizeEquivTables (n : Nat) :
    {A : FinitePartialCode db du dd // A.size = n} ≃
      FinitePartialTables db du dd n where
  toFun A := by
    rcases A with ⟨⟨m,b,u,d,e⟩,h⟩
    change m = n at h
    subst m
    exact (b,u,d,e)
  invFun T := ⟨⟨n,T.1,T.2.1,T.2.2.1,T.2.2.2⟩,rfl⟩
  left_inv A := by
    rcases A with ⟨⟨m,b,u,d,e⟩,h⟩
    change m = n at h
    subst m
    rfl
  right_inv T := by
    rcases T with ⟨b,u,d,e⟩
    rfl

/-- Layer n consists of the valid vertices of size n+1, so there is no
empty-code layer to enumerate. -/
abbrev Layer (family : List (NormalizedForbidden db du dd)) (n : Nat) :=
  {A : FiniteGPlusVertex family // A.val.size = n+1}

/-- Validity is a predicate on finite tables, not additional infinite data. -/
noncomputable instance layerFintype
    (family : List (NormalizedForbidden db du dd)) (n : Nat) :
    Fintype (Layer family n) := by
  classical
  letI : Fintype {A : FinitePartialCode db du dd // A.size = n+1} :=
    Fintype.ofEquiv (FinitePartialTables db du dd (n+1))
      (fixedSizeEquivTables (n+1)).symm
  let f : Layer family n →
      {A : FinitePartialCode db du dd // A.size = n+1} :=
    fun A => ⟨A.val.val,A.property⟩
  apply Fintype.ofInjective f
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun X : {A : FinitePartialCode db du dd // A.size = n+1} => X.val) h

noncomputable def width (family : List (NormalizedForbidden db du dd)) (n : Nat) : Nat :=
  Fintype.card (Layer family n)

/-- An actual countable C+ witnesses nonemptiness of every positive layer.
For the manuscript application C+ is the already constructed numerical H+. -/
theorem width_pos
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (n : Nat) :
    0 < width family n := by
  exact Fintype.card_pos_iff.mpr ⟨⟨C.toGPlus family hAvoid n,rfl⟩⟩

/-- Forget the layer tag, which is already determined by the code's size. -/
def flatten (family : List (NormalizedForbidden db du dd)) :
    (Σ n : Nat, Layer family n) → FiniteGPlusVertex family :=
  fun A => A.2.val

theorem flatten_bijective (family : List (NormalizedForbidden db du dd)) :
    Function.Bijective (flatten family) := by
  constructor
  · rintro ⟨n,⟨A,hA⟩⟩ ⟨m,⟨B,hB⟩⟩ h
    change A = B at h
    subst B
    have hnm : n = m := by omega
    subst m
    rfl
  · intro A
    have hPos := finiteGPlusVertex_size_pos A
    refine ⟨⟨A.val.size-1,⟨A,?_⟩⟩,rfl⟩
    omega

noncomputable def flattenEquiv (family : List (NormalizedForbidden db du dd)) :
    (Σ n : Nat, Layer family n) ≃ FiniteGPlusVertex family :=
  Equiv.ofBijective (flatten family) (flatten_bijective family)

/-- Choose finite numberings inside the individual layers; their first
coordinate remains the prescribed size index. -/
noncomputable def numberedEquiv (family : List (NormalizedForbidden db du dd)) :
    (Σ n : Nat, Layer family n) ≃ (Σ n : Nat, Fin (width family n)) :=
  Equiv.sigmaCongrRight (fun n => Fintype.equivFin (Layer family n))

/-- The exhaustive, repetition-free enumeration of all genuine G+ vertices. -/
noncomputable def enumerate
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    Nat ≃ FiniteGPlusVertex family :=
  (((FiniteLayerEnumeration.rankEquiv (width family)
    (width_pos C family hAvoid)).symm.trans (numberedEquiv family).symm).trans
    (flattenEquiv family))

/-- The enumeration really has the size of its selected finite layer. -/
theorem enumerate_size
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (m : Nat) :
    (enumerate C family hAvoid m).val.size =
      ((FiniteLayerEnumeration.rankEquiv (width family)
        (width_pos C family hAvoid)).symm m).1 + 1 := by
  let z := (FiniteLayerEnumeration.rankEquiv (width family)
    (width_pos C family hAvoid)).symm m
  change ((numberedEquiv family).symm z).2.val.val.size = z.1+1
  exact ((numberedEquiv family).symm z).2.property

/-- Equal-size vertices may occur consecutively; sizes never decrease. -/
theorem enumerate_size_mono
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    Monotone (fun m : Nat => (enumerate C family hAvoid m).val.size) := by
  intro i j hij
  change (enumerate C family hAvoid i).val.size ≤
    (enumerate C family hAvoid j).val.size
  rw [enumerate_size, enumerate_size]
  exact Nat.add_le_add_right
    (FiniteLayerEnumeration.rankEquiv_symm_layer_mono (width family)
      (width_pos C family hAvoid) hij) 1

/-- The actual enumerated G-omega L-reduct omits the forbidden family.
The enumeration here is constructed above, not supplied as an interface. -/
theorem enumeratedL_avoids_family
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    ∀ bad, bad ∈ family →
      bad.Avoids (finiteGPlusEnumeratedL (enumerate C family hAvoid)) :=
  finiteGPlusEnumeratedL_avoids_family (enumerate C family hAvoid)
    (enumerate_size_mono C family hAvoid)

end SuccessorTree.V10.GPlusEnumeration
