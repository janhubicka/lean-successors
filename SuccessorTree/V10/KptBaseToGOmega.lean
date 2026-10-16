import SuccessorTree.V10.GPlusOrderedEmbedding
import SuccessorTree.V10.HInfiniteBaseEmbedding
import Mathlib.Tactic

/-!
# The ordered base K embeds through H+ into the actual G-omega

The normalized finite unary/directed-binary/diagonal language already
has (a) an induced ordered top-generation copy of the full-carrier K
inside the genuine countable numerical H, and (b) an ordered induced
embedding of the genuine countable H+ into an exhaustive, size-ordered
enumeration of all finite G+ vertices.

This file composes those existing Lean statements at the exact
InducedEmbedding interface, with the same K and the same numerical H+.
The composition preserves **all** present and absent directed binary,
unary and diagonal facts; E is used only where it is actually defined
for H+.

An exhaustive G-omega enumeration is constructed by layers of finite
codes, and its use of an auxiliary countable H+ is confined to a proof
that every positive layer is nonempty. That proof is irrelevant to the
enumeration as a function. Consequently one fixed reference witness
suffices for all K in the same forbidden age.

This establishes the literal normalized ordered embedding leg of
Section 6. It does not imply the remaining uniform envelope/colouring
statement for arbitrary A-copies or the original unqualified theorem.
-/

namespace SuccessorTree.V10

/-- Composition of the existing ordered, full-induced L-embeddings.
No category-theoretic infrastructure or weakened notion of embedding
is needed; distinct-pair binary facts and singleton atoms transport
separately and exactly. -/
def AgeTestModel.InducedEmbedding.comp
    {db du dd : Nat}
    {A B C : AgeTestModel db du dd}
    (g : B.InducedEmbedding C)
    (f : A.InducedEmbedding B) :
    A.InducedEmbedding C where
  toFun := fun x => g.toFun (f.toFun x)
  strictMono := g.strictMono.comp f.strictMono
  inside := by
    intro x hx
    exact g.inside (f.toFun x) (f.inside x hx)
  binary := by
    intro x y hx hy hxy t
    have hfxy : f.toFun x ≠ f.toFun y := by
      intro heq
      exact hxy (f.strictMono.injective heq)
    exact (g.binary (f.toFun x) (f.toFun y)
      (f.inside x hx) (f.inside y hy) hfxy t).trans
      (f.binary x y hx hy hxy t)
  unary := by
    intro x hx t
    exact (g.unary (f.toFun x) (f.inside x hx) t).trans
      (f.unary x hx t)
  diagonal := by
    intro x hx t
    exact (g.diagonal (f.toFun x) (f.inside x hx) t).trans
      (f.diagonal x hx t)

/-- The actual top-generation coordinate injection is an ordered,
induced embedding of the base K into the numerical countable H.
This is the direct structure-valued form of the previously checked
six-clause finite-record theorem. -/
noncomputable def infiniteNumericHL_top_induced_embedding
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (k : Nat) :
    K.InducedEmbedding (infiniteNumericHL K k) := by
  obtain ⟨hInside, _hInjective, hStrict,
    hBinary, hUnary, hDiagonal⟩ :=
    infiniteNumericHL_top_induced_ordered_copy K hCarrier k
  exact {
    toFun := fun i => hPosition k i k
    strictMono := hStrict
    inside := by intro i _hi; exact hInside i
    binary := by
      intro i j _hi _hj hij t
      exact hBinary i j hij t
    unary := by
      intro i _hi t
      exact hUnary i t
    diagonal := by
      intro i _hi t
      exact hDiagonal i t
  }

/-- The *same* H+ from the verified numerical construction connects
the actual K top-generation copy to the actual exhaustive G-omega
enumeration. Neither embedding is a chosen external hypothesis. -/
noncomputable def infiniteNumericKToGOmega
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) :
    K.InducedEmbedding
      (finiteGPlusEnumeratedL
        (GPlusEnumeration.enumerate (infiniteNumericHPlus K k) family
          (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k))) :=
  (infiniteNumericHPlusToGOmega family K hCarrier hAvoidK k).comp
    (infiniteNumericHL_top_induced_embedding K hCarrier k)

/-- The complete finite-layer enumeration of G+ does not depend on
the auxiliary countable forbidden-free partial structure used to
witness nonemptiness of each layer. All its occurrences in the
enumeration definition are proof terms. -/
theorem GPlusEnumeration.enumerate_independent_of_witness
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C D : CountableEnumeratedPartialStructure db du dd)
    (hC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (hD : ∀ bad, bad ∈ family → bad.Avoids D.L) :
    GPlusEnumeration.enumerate C family hC =
      GPlusEnumeration.enumerate D family hD := by
  rfl

/-- A FIXED reference countable forbidden-free C+ determines one
size-ordered exhaustive enumeration of all G+ codes. Every
full-carrier, forbidden-free normalized K embeds inducedly and
order-preservingly into that very same G-omega structure. -/
noncomputable def infiniteNumericKToFixedGOmega
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (C : CountableEnumeratedPartialStructure db du dd)
    (hAvoidC : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) :
    K.InducedEmbedding
      (finiteGPlusEnumeratedL
        (GPlusEnumeration.enumerate C family hAvoidC)) := by
  have hEq :
      GPlusEnumeration.enumerate (infiniteNumericHPlus K k) family
        (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k) =
      GPlusEnumeration.enumerate C family hAvoidC :=
    GPlusEnumeration.enumerate_independent_of_witness family
      (infiniteNumericHPlus K k) C
      (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)
      hAvoidC
  rw [← hEq]
  exact infiniteNumericKToGOmega family K hCarrier hAvoidK k

end SuccessorTree.V10
