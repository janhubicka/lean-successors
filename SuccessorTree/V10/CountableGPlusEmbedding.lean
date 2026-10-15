import SuccessorTree.V10.GPlusEnumeratedAge
import SuccessorTree.V10.HCountablePartialTower

/-!
# The canonical induced embedding of a countable partial structure into G+

For a forbidden-free countable enumerated partial structure C+, send vertex
v to the finite on-carrier code of C+ restricted to its first v+1 vertices.
This is an actual valid G+ vertex, not an assumed representation witness.
Its size is v+1; its last coordinate is v. Prefix coherence therefore makes
all directed off-diagonal binary, unary, diagonal and E atoms agree exactly.
In particular the map is injective and is strictly increasing in size.

The construction applies to the already verified countable numerical H+.
It precedes the separate exhaustive G-omega enumeration and final Ramsey
transfer; neither of those later steps is assumed or asserted here.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}

namespace CountableEnumeratedPartialStructure

/-- The literal finite on-carrier table of a countable partial structure. -/
def prefixCode (C : CountableEnumeratedPartialStructure db du dd) (N : Nat) :
    FinitePartialCode db du dd where
  size := N
  binary := fun i j t => C.L.binary i.val j.val t
  unary := fun i t => C.L.unary i.val t
  diagonal := fun i t => C.L.diagonal i.val t
  eRelation := fun i j => C.E i.val j.val

/-- This table is precisely the code of the genuine finite partial prefix.
Clipping its E target does not change any on-carrier value. -/
theorem ofEnumerated_finitePrefix
    (C : CountableEnumeratedPartialStructure db du dd) (N : Nat) :
    FinitePartialCode.ofEnumerated (C.finitePrefix N) = C.prefixCode N := by
  simp [FinitePartialCode.ofEnumerated, finitePrefix, prefixCode]

/-- Finite-code restriction agrees literally with the shorter prefix. -/
theorem prefixCode_restrict
    (C : CountableEnumeratedPartialStructure db du dd)
    (M N : Nat) (hMN : M ≤ N) :
    (C.prefixCode N).restrict M hMN = C.prefixCode M := rfl

/-- A forbidden copy in a finite prefix is already a copy in C. -/
theorem realizes_of_finitePrefix
    {r : Nat} (C : CountableEnumeratedPartialStructure db du dd)
    (N : Nat) (F : ForbiddenAtomicPattern r db du dd) (f : Fin r → Nat)
    (hCopy : (C.finitePrefix N).L.Realizes F f) : C.L.Realizes F f :=
  ⟨hCopy.1, fun a => C.fullCarrier (f a),
    hCopy.2.2.1, hCopy.2.2.2.1, hCopy.2.2.2.2⟩

/-- Prefix avoidance is inherited for both singleton and nontrivial
forbidden patterns, with all induced atomic data retained. -/
theorem finitePrefix_avoids_family
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (N : Nat) :
    ∀ bad, bad ∈ family → bad.Avoids (C.finitePrefix N).L := by
  intro bad hMem
  cases bad with
  | singleton F hNeutral =>
      rintro ⟨f,hCopy⟩
      exact hAvoid (.singleton F hNeutral) hMem
        ⟨f,C.realizes_of_finitePrefix N F f hCopy⟩
  | nontrivial r F hr hIrred =>
      rintro ⟨f,hCopy⟩
      exact hAvoid (.nontrivial r F hr hIrred) hMem
        ⟨f,C.realizes_of_finitePrefix N F f hCopy⟩

/-- The canonical vertex map C+ → G+: v maps to the code on v+1 vertices. -/
def toGPlus
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (v : Nat) : FiniteGPlusVertex family :=
  ⟨C.prefixCode (v+1), C.finitePrefix (v+1),
    (C.ofEnumerated_finitePrefix (v+1)).symm,
    Nat.zero_lt_succ v, C.finitePrefix_avoids_family family hAvoid (v+1)⟩

@[simp] theorem toGPlus_size
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (v : Nat) :
    (C.toGPlus family hAvoid v).val.size = v+1 := rfl

/-- The canonical map follows one strict prefix chain in G+. -/
theorem toGPlus_properPrefix
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    {u v : Nat} (huv : u < v) :
    (C.toGPlus family hAvoid u).IsProperPrefix
      (C.toGPlus family hAvoid v) := by
  have hLe : u+1 ≤ v+1 := by omega
  refine ⟨⟨hLe, ?_⟩, ?_⟩
  · exact (C.prefixCode_restrict (u+1) (v+1) hLe).symm
  · change u+1 < v+1
    omega

theorem toGPlus_strictMono_size
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    StrictMono (fun v : Nat => (C.toGPlus family hAvoid v).val.size) := by
  intro u v huv
  exact (C.toGPlus_properPrefix family hAvoid huv).2

/-- Distinct vertices have distinct code lengths, hence distinct G+ images. -/
theorem toGPlus_injective
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    Function.Injective (C.toGPlus family hAvoid) := by
  intro u v huv
  apply (C.toGPlus_strictMono_size family hAvoid).injective
  exact congrArg (fun A : FiniteGPlusVertex family => A.val.size) huv

/-- Both binary orientations, including absence of atoms, are preserved. -/
theorem toGPlus_binary
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    {u v : Nat} (huv : u ≠ v) (t : Fin db) :
    finiteGPlusBinary (C.toGPlus family hAvoid u)
      (C.toGPlus family hAvoid v) t = C.L.binary u v t := by
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · rw [finiteGPlusBinary_forward _ _ t
      (C.toGPlus_properPrefix family hAvoid hlt)]
    simp [FiniteGPlusVertex.lowerLastIn, FiniteGPlusVertex.last,
      toGPlus, prefixCode]
  · rw [finiteGPlusBinary_reverse _ _ t
      (C.toGPlus_properPrefix family hAvoid hgt)]
    simp [FiniteGPlusVertex.lowerLastIn, FiniteGPlusVertex.last,
      toGPlus, prefixCode]

theorem toGPlus_unary
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (v : Nat) (t : Fin du) :
    finiteGPlusUnary (C.toGPlus family hAvoid v) t = C.L.unary v t := by
  simp [finiteGPlusUnary, FiniteGPlusVertex.last, toGPlus, prefixCode]

theorem toGPlus_diagonal
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L)
    (v : Nat) (t : Fin dd) :
    finiteGPlusDiagonal (C.toGPlus family hAvoid v) t = C.L.diagonal v t := by
  simp [finiteGPlusDiagonal, FiniteGPlusVertex.last, toGPlus, prefixCode]

/-- The auxiliary relation is preserved on all ordered pairs, including
reversed pairs and the diagonal. Only the original E of C+ is used. -/
theorem toGPlus_E
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) (u v : Nat) :
    finiteGPlusE (C.toGPlus family hAvoid u)
      (C.toGPlus family hAvoid v) = C.E u v := by
  rcases lt_trichotomy u v with hlt | heq | hgt
  · rw [finiteGPlusE_forward _ _ (C.toGPlus_properPrefix family hAvoid hlt)]
    simp [FiniteGPlusVertex.lowerLastIn, FiniteGPlusVertex.last,
      toGPlus, prefixCode]
  · subst v
    have hNot : ¬ (C.toGPlus family hAvoid u).IsProperPrefix
        (C.toGPlus family hAvoid u) := fun h => Nat.lt_irrefl _ h.2
    have hE : C.E u u = false := by
      cases he : C.E u u with
      | false => rfl
      | true =>
          have hs := C.spaced u u he
          omega
    simp [finiteGPlusE, hNot, hE]
  · have hPrefix := C.toGPlus_properPrefix family hAvoid hgt
    have hNot := FiniteGPlusVertex.properPrefix_asymm hPrefix
    simp only [finiteGPlusE, dif_neg hNot, dif_pos hPrefix]
    simp [FiniteGPlusVertex.lowerLastIn, FiniteGPlusVertex.last,
      toGPlus, prefixCode]

/-- Pulling back the G+ L-reduct along the actual canonical map is exactly
C on its carrier: all singleton data and off-diagonal directed atoms agree.
This is an induced embedding, not merely a homomorphism. -/
theorem toGPlus_induced
    (C : CountableEnumeratedPartialStructure db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hAvoid : ∀ bad, bad ∈ family → bad.Avoids C.L) :
    Function.Injective (C.toGPlus family hAvoid) ∧
    StrictMono (fun v : Nat => (C.toGPlus family hAvoid v).val.size) ∧
    (∀ u v : Nat, u ≠ v → ∀ t : Fin db,
      finiteGPlusBinary (C.toGPlus family hAvoid u)
        (C.toGPlus family hAvoid v) t = C.L.binary u v t) ∧
    (∀ v : Nat, ∀ t : Fin du,
      finiteGPlusUnary (C.toGPlus family hAvoid v) t = C.L.unary v t) ∧
    (∀ v : Nat, ∀ t : Fin dd,
      finiteGPlusDiagonal (C.toGPlus family hAvoid v) t = C.L.diagonal v t) ∧
    (∀ u v : Nat, finiteGPlusE (C.toGPlus family hAvoid u)
      (C.toGPlus family hAvoid v) = C.E u v) :=
  ⟨C.toGPlus_injective family hAvoid,
    C.toGPlus_strictMono_size family hAvoid,
    fun _ _ h t => C.toGPlus_binary family hAvoid h t,
    C.toGPlus_unary family hAvoid, C.toGPlus_diagonal family hAvoid,
    C.toGPlus_E family hAvoid⟩

end CountableEnumeratedPartialStructure

/-- Apply the generic construction to the manuscript's actual numerical H+.
Its forbidden avoidance is proved by the finite-H argument, not supplied
as a new hypothesis. -/
noncomputable def infiniteNumericHPlusToGPlus
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) : Nat → FiniteGPlusVertex family :=
  (infiniteNumericHPlus K k).toGPlus family
    (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)

/-- The concrete numerical H+ map is an induced L+ embedding with
strictly increasing code lengths. -/
theorem infiniteNumericHPlusToGPlus_induced
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k : Nat) :
    let f := infiniteNumericHPlusToGPlus family K hCarrier hAvoidK k
    Function.Injective f ∧
    StrictMono (fun v : Nat => (f v).val.size) ∧
    (∀ u v : Nat, u ≠ v → ∀ t : Fin db,
      finiteGPlusBinary (f u) (f v) t = (infiniteNumericHL K k).binary u v t) ∧
    (∀ v : Nat, ∀ t : Fin du,
      finiteGPlusUnary (f v) t = (infiniteNumericHL K k).unary v t) ∧
    (∀ v : Nat, ∀ t : Fin dd,
      finiteGPlusDiagonal (f v) t = (infiniteNumericHL K k).diagonal v t) ∧
    (∀ u v : Nat, finiteGPlusE (f u) (f v) = (infiniteNumericHPlus K k).E u v) :=
  (infiniteNumericHPlus K k).toGPlus_induced family
    (infiniteNumericHL_avoids_family family K hCarrier hAvoidK k)

end SuccessorTree.V10
