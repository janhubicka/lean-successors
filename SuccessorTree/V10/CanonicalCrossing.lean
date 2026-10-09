import SuccessorTree.V10.CanonicalInsertionParameter
import Mathlib.Tactic

/-!
# No-new-tuples part of the concrete partial-type successor

For the newly introduced ordinary vertex v in a finite enumerated
partial structure, write f = fl(v), its uniquely determined first
missing E-coordinate. The E-socle of v is exactly the initial
segment [0,f). By the third partial-structure axiom, every binary
L-relation joining an earlier vertex u<v to v forces E(u,v).

Consequently ALL directed binary tuples between v and old coordinates
f<=u<v are absent. Below f, the new tuples are precisely those
recorded by the actual partial type of v over its E-socle. This is
the no-new-tuples portion of Definition 6.30, for every positive
and negative directed binary bit, with no extra assumption.

This does not yet implement a forward successor function nor prove
the S2/S3 decomposition properties. The terminal one-step
letter recording the relation between v and the distinguished type
vertex will be formalized separately.
-/

namespace SuccessorTree.V10

/-- Beyond the first missing coordinate there are no further
auxiliary E-pairs to the new ordinary vertex. -/
theorem E_false_at_or_above_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) (hu : A.freeLevel v ≤ u) :
    A.E u v = false := by
  cases he : A.E u v with
  | false => rfl
  | true =>
      have hlt := (A.E_iff_freeLevel u v).mp he
      omega

/-- Any directed binary pair joining a new ordinary vertex to an
earlier coordinate beyond the free E-cut must be empty.
Both orientations and all negative binary bits are covered. -/
theorem binary_false_at_or_above_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) (huv : u < v)
    (huSize : u < A.size) (hvSize : v < A.size)
    (hu : A.freeLevel v ≤ u)
    (r : Fin db) :
    A.L.binary u v r = false ∧
      A.L.binary v u r = false := by
  have hNot : A.E u v = false :=
    E_false_at_or_above_freeLevel A u v hu
  constructor
  · cases hb : A.L.binary u v r with
    | false => rfl
    | true =>
        have he := A.linked_E u v huv huSize hvSize
          ⟨r, Or.inl hb⟩
        have hf := (A.E_iff_freeLevel u v).mp he
        omega
  · cases hb : A.L.binary v u r with
    | false => rfl
    | true =>
        have he := A.linked_E u v huv huSize hvSize
          ⟨r, Or.inr hb⟩
        have hf := (A.E_iff_freeLevel u v).mp he
        omega

/-- The directed atomic tuple of the new vertex over the initial
E-socle is the corresponding tuple of its canonical parameter.
This is exact equality, not just one-way containment. -/
theorem binary_at_freeSocle_eq_parameter
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) (hu : u < A.freeLevel v)
    (r : Fin db) :
    (A.partialTypeAt (A.freeLevel v) v).lReduct.binary
        (some ⟨u, hu⟩) none r = A.L.binary u v r ∧
      (A.partialTypeAt (A.freeLevel v) v).lReduct.binary
        none (some ⟨u, hu⟩) r = A.L.binary v u r := by
  exact ⟨rfl, rfl⟩

/-- The complete E-column is fixed by its free cut. In particular
the parameter prescribes every positive E-pair and no E-pair
beyond the cut may be added by a successor operation. -/
theorem E_eq_decide_freeLevel
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) :
    A.E u v = decide (u < A.freeLevel v) := by
  by_cases hu : u < A.freeLevel v
  · have he := (A.E_iff_freeLevel u v).mpr hu
    simp [hu, he]
  · have he := E_false_at_or_above_freeLevel A u v (by omega)
    simp [hu, he]

/-- Complete reconstruction of the forward directed cross-tuple:
copy the canonical parameter below the free cut and put zero
above it. -/
def canonicalCrossForward
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v u : Nat) (r : Fin db) : Bool :=
  if h : u < A.freeLevel v then
    (A.partialTypeAt (A.freeLevel v) v).lReduct.binary
      (some ⟨u, h⟩) none r
  else false

/-- Complete reconstruction of the backward directed cross-tuple. -/
def canonicalCrossBackward
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (v u : Nat) (r : Fin db) : Bool :=
  if h : u < A.freeLevel v then
    (A.partialTypeAt (A.freeLevel v) v).lReduct.binary
      none (some ⟨u, h⟩) r
  else false

/-- All binary tuples between the new ordinary vertex and any earlier
coordinate are uniquely determined by the canonical E-socle
parameter and the no-new-tuples rule. -/
theorem canonicalCross_eq_actual
    {db du dd : Nat}
    (A : EnumeratedPartialStructure db du dd)
    (u v : Nat) (huv : u < v)
    (huSize : u < A.size) (hvSize : v < A.size)
    (r : Fin db) :
    canonicalCrossForward A v u r = A.L.binary u v r ∧
      canonicalCrossBackward A v u r = A.L.binary v u r := by
  by_cases hu : u < A.freeLevel v
  · exact ⟨by simp [canonicalCrossForward, hu,
          EnumeratedPartialStructure.partialTypeAt,
          RelationalPrefixType.ofAgeModel, prefixVertexIndex],
        by simp [canonicalCrossBackward, hu,
          EnumeratedPartialStructure.partialTypeAt,
          RelationalPrefixType.ofAgeModel, prefixVertexIndex]⟩
  · have hzero := binary_false_at_or_above_freeLevel A
      u v huv huSize hvSize (by omega) r
    exact ⟨by simp [canonicalCrossForward, hu, hzero.1],
      by simp [canonicalCrossBackward, hu, hzero.2]⟩

end SuccessorTree.V10
