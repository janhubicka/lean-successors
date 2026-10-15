import SuccessorTree.V10.GPlusSizeEnumeration
import SuccessorTree.V10.M2InducedAgeTransfer

/-!
# Ordered induced embeddings into the actual enumeration of G+

Compose the canonical prefix-code map with the inverse of the genuine
size-nondecreasing enumeration. Its numerical ranks strictly increase:
otherwise monotonicity of the enumeration would reverse two strictly
increasing prefix sizes. All induced atoms are transported by the two
inverse identities of the enumeration, not an assumed representation.

This supplies the ordered H-to-G-omega bridge and the forbidden-free
G-omega model. The envelope-to-Ramsey assembly remains a separate step.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

namespace CountableEnumeratedPartialStructure

/-- The actual index of the canonical prefix code in the exhaustive enumeration. -/
noncomputable def toGOmega
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (v : Nat) : Nat :=
  (GPlusEnumeration.enumerate C family hAvoid).symm (C.toGPlus family hAvoid v)

/-- Decoding this rank recovers the whole genuine finite code. -/
theorem toGOmega_eval
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (v : Nat) :
    GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid v) =
      C.toGPlus family hAvoid v :=
  (GPlusEnumeration.enumerate C family hAvoid).apply_symm_apply _

/-- Strictly increasing prefix sizes force strictly increasing enumeration ranks. -/
theorem toGOmega_strictMono
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    StrictMono (C.toGOmega family hAvoid) := by
  intro u v huv
  by_contra h
  have hRank : C.toGOmega family hAvoid v ≤ C.toGOmega family hAvoid u :=
    Nat.le_of_not_gt h
  have hs := GPlusEnumeration.enumerate_size_mono C family hAvoid hRank
  change
    (GPlusEnumeration.enumerate C family hAvoid
      (C.toGOmega family hAvoid v)).val.size ≤
    (GPlusEnumeration.enumerate C family hAvoid
      (C.toGOmega family hAvoid u)).val.size at hs
  rw [C.toGOmega_eval family hAvoid v, C.toGOmega_eval family hAvoid u,
    C.toGPlus_size family hAvoid v, C.toGPlus_size family hAvoid u] at hs
  omega

/-- An actual ordered induced L-embedding into the constructed G-omega reduct.
The established reusable induced-embedding structure is used directly. -/
noncomputable def toGOmega_induced
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    C.L.InducedEmbedding
      (finiteGPlusEnumeratedL (GPlusEnumeration.enumerate C family hAvoid)) where
  toFun := C.toGOmega family hAvoid
  strictMono := C.toGOmega_strictMono family hAvoid
  inside := by intro _ _; trivial
  binary := by
    intro u v _ _ huv t
    change finiteGPlusBinary
      (GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid u))
      (GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid v)) t =
      C.L.binary u v t
    rw [C.toGOmega_eval family hAvoid u, C.toGOmega_eval family hAvoid v]
    exact C.toGPlus_binary family hAvoid huv t
  unary := by
    intro v _ t
    change finiteGPlusUnary
      (GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid v)) t =
      C.L.unary v t
    rw [C.toGOmega_eval family hAvoid v]
    exact C.toGPlus_unary family hAvoid v t
  diagonal := by
    intro v _ t
    change finiteGPlusDiagonal
      (GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid v)) t =
      C.L.diagonal v t
    rw [C.toGOmega_eval family hAvoid v]
    exact C.toGPlus_diagonal family hAvoid v t

/-- The auxiliary E atoms also agree on every ordered pair of image ranks. -/
theorem toGOmega_E
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (u v : Nat) :
    finiteGPlusE
      (GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid u))
      (GPlusEnumeration.enumerate C family hAvoid (C.toGOmega family hAvoid v)) =
      C.E u v := by
  rw [C.toGOmega_eval family hAvoid u, C.toGOmega_eval family hAvoid v]
  exact C.toGPlus_E family hAvoid u v

end CountableEnumeratedPartialStructure

/-- The actual numerical H embeds into the actual forbidden-free G-omega
L-reduct; both the H avoidance proof and the exhaustive enumeration are
constructed, not new hypotheses at this endpoint. -/
noncomputable def infiniteNumericHPlusToGOmega
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) :
    (infiniteNumericHL K k).InducedEmbedding
      (finiteGPlusEnumeratedL
        (GPlusEnumeration.enumerate (infiniteNumericHPlus K k) family
          (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k))) :=
  (infiniteNumericHPlus K k).toGOmega_induced family
    (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)

/-- The target of the concrete ordered H embedding omits the entire family. -/
theorem infiniteNumericHPlusGOmega_avoids_family
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) :
    ∀ bad, bad ∈ family → bad.Avoids
      (finiteGPlusEnumeratedL
        (GPlusEnumeration.enumerate (infiniteNumericHPlus K k) family
          (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k))) :=
  GPlusEnumeration.enumeratedL_avoids_family (infiniteNumericHPlus K k) family
    (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)

end SuccessorTree.V10
