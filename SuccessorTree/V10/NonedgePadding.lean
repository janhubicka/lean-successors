import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Source-side non-edge padding, relative to an unchanged initial socle

Keep the first `n` vertices, and put every later vertex at
`n + 1 + 2 * (i - n)`. All other positions have the allowed neutral
singleton and no L-relations. This preserves the entire induced L-age:
an irreducible forbidden copy cannot contain a padding vertex.

An existing E-socle on the first n vertices extends to the padded
structure. At each real upper vertex use the maximal spaced E-column;
at a new neutral vertex use the empty E-column. No E-expansion of the
un-padded numerical layout, and no B3 hypothesis, is needed.

This is the concrete finite padding input for the M2 argument. The
transport of these witnesses by an arbitrary ShapeMap is separate.
-/

namespace SuccessorTree.V10
namespace NonedgePadding

/-- A padding position is real precisely in the retained initial socle
or at an odd offset from its boundary. -/
def Real (n x : Nat) : Prop := x < n ∨ (x - n) % 2 = 1

instance (n x : Nat) : Decidable (Real n x) := by
  unfold Real
  infer_instance

/-- The old address carried by a real position. -/
def project (n x : Nat) : Nat :=
  if x < n then x else n + (x - n) / 2

/-- The new address of an old vertex. -/
def address (n i : Nat) : Nat :=
  if i < n then i else n + 1 + 2 * (i - n)

/-- Includes a final neutral position, also when the upper tail is empty. -/
def size (n N : Nat) : Nat := n + 2 * (N - n) + 1

theorem size_ge (n N : Nat) : n ≤ size n N := by
  unfold size
  omega

theorem address_real (n i : Nat) : Real n (address n i) := by
  unfold Real address
  split_ifs <;> omega

theorem project_address (n i : Nat) : project n (address n i) = i := by
  unfold project address
  split_ifs <;> omega

theorem address_lt_size (n N i : Nat) (hi : i < N) :
    address n i < size n N := by
  unfold address size
  split_ifs <;> omega

theorem project_lt (n N x : Nat) (hn : n ≤ N)
    (hx : x < size n N) (hReal : Real n x) :
    project n x < N := by
  unfold project size Real at *
  split_ifs <;> omega

theorem project_lt_project (n x y : Nat)
    (hx : Real n x) (hy : Real n y) (hxy : x < y) :
    project n x < project n y := by
  unfold project Real at *
  split_ifs <;> omega

/-- Every real upper vertex is separated from every earlier real vertex. -/
theorem upper_spacing (n x y : Nat)
    (hx : Real n x) (hy : Real n y)
    (hUpper : n ≤ y) (hxy : x < y) :
    x + 1 < y := by
  unfold Real at *
  omega

/-- Copy all atoms at real positions, and add only neutral non-edges. -/
def model {db du dd : Nat}
    (A : AgeTestModel db du dd) (n N : Nat) :
    AgeTestModel db du dd where
  carrier := {x | x < size n N}
  binary := fun x y t =>
    if Real n x ∧ Real n y then
      A.binary (project n x) (project n y) t else false
  unary := fun x t =>
    if Real n x then A.unary (project n x) t else false
  diagonal := fun x t =>
    if Real n x then A.diagonal (project n x) t else false

/-- Any complete induced copy supported on real positions projects back
with every positive and negative atom and with its order unchanged. -/
theorem realizes_projects {r db du dd : Nat}
    (A : AgeTestModel db du dd) (n N : Nat) (hn : n ≤ N)
    (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (P : ForbiddenAtomicPattern r db du dd) (e : Fin r → Nat)
    (hCopy : (model A n N).Realizes P e)
    (hReal : ∀ a, Real n (e a)) :
    A.Realizes P (fun a => project n (e a)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact project_lt_project n (e a) (e b)
      (hReal a) (hReal b) (hCopy.1 hab)
  · intro a
    exact (hCarrier _).2
      (project_lt n N (e a) hn (hCopy.2.1 a) (hReal a))
  · intro a b hab t
    simpa [model, hReal a, hReal b] using
      hCopy.2.2.1 a b hab t
  · intro a t
    simpa only [model, if_pos (hReal a)] using hCopy.2.2.2.1 a t
  · intro a t
    simpa only [model, if_pos (hReal a)] using hCopy.2.2.2.2 a t

/-- A nontrivial irreducible copy cannot use a new non-edge vertex. -/
theorem irreducible_copy_real {r db du dd : Nat}
    (A : AgeTestModel db du dd) (n N : Nat)
    (P : ForbiddenAtomicPattern r db du dd)
    (hr : 1 < r) (hIrred : P.Irreducible)
    (e : Fin r → Nat) (hCopy : (model A n N).Realizes P e) :
    ∀ a, Real n (e a) := by
  intro a
  by_contra ha
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1,hr⟩
  have hzo : z ≠ o := by
    intro h
    have hh := congrArg Fin.val h
    norm_num [z,o] at hh
  obtain ⟨b,hab⟩ : ∃ b : Fin r, a ≠ b := by
    by_cases haz : a = z
    · exact ⟨o,by simpa [haz] using hzo⟩
    · exact ⟨z,haz⟩
  obtain ⟨t,ht | ht⟩ := hIrred a b hab
  · have h := hCopy.2.2.1 a b hab t
    simp [model,ha,ht] at h
  · have h := hCopy.2.2.1 b a hab.symm t
    simp [model,ha,ht] at h

/-- No normalized forbidden pattern is introduced by any number of
neutral padding positions. Singleton obstructions are checked too. -/
theorem preserves_avoidance {db du dd : Nat}
    (A : AgeTestModel db du dd) (n N : Nat) (hn : n ≤ N)
    (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (bad : NormalizedForbidden db du dd)
    (hAvoid : bad.Avoids A) :
    bad.Avoids (model A n N) := by
  cases bad with
  | singleton P hNeutral =>
      rintro ⟨e,he⟩
      have hReal : ∀ a : Fin 1, Real n (e a) := by
        intro a
        have ha : a = 0 := Subsingleton.elim _ _
        subst a
        by_contra hNot
        rcases hNeutral with ⟨t,ht⟩ | ⟨t,ht⟩
        · have h := he.2.2.2.1 0 t
          simp [model,hNot,ht] at h
        · have h := he.2.2.2.2 0 t
          simp [model,hNot,ht] at h
      exact hAvoid ⟨_,realizes_projects A n N hn hCarrier P e he hReal⟩
  | nontrivial r P hr hIrred =>
      rintro ⟨e,he⟩
      exact hAvoid ⟨_,realizes_projects A n N hn hCarrier P e he
        (irreducible_copy_real A n N P hr hIrred e he)⟩

/-- The old model is an ordered induced substructure of its padding. -/
theorem realizes_at_addresses {r db du dd : Nat}
    (A : AgeTestModel db du dd) (n N : Nat)
    (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (P : ForbiddenAtomicPattern r db du dd) (e : Fin r → Nat)
    (hCopy : A.Realizes P e) :
    (model A n N).Realizes P (fun a => address n (e a)) := by
  have hAddr : StrictMono (address n) := by
    intro x y hxy
    unfold address
    split_ifs <;> omega
  refine ⟨hAddr.comp hCopy.1,?_,?_,?_,?_⟩
  · intro a
    exact address_lt_size n N (e a) ((hCarrier _).1 (hCopy.2.1 a))
  · intro a b hab t
    simpa [model,address_real,project_address] using hCopy.2.2.1 a b hab t
  · intro a t
    simpa [model,address_real,project_address] using hCopy.2.2.2.1 a t
  · intro a t
    simpa [model,address_real,project_address] using hCopy.2.2.2.2 a t

/-- Keep the original E-socle. Real upper vertices get maximal spaced
columns; neutral upper vertices have empty columns. -/
def E {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd) (n N u v : Nat) : Bool :=
  if v < n then C.E u v
  else decide (v < size n N ∧ Real n v ∧ u + 1 < v)

/-- The source-side padding supplies a genuine E-expansion relative to
ANY fixed compatible initial E-socle, even when the old numerical
layout itself has consecutive L-linked upper vertices. -/
def partialStructure {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t) :
    EnumeratedPartialStructure db du dd where
  size := size n N
  L := model A n N
  carrier_iff := fun _ => Iff.rfl
  E := E C n N
  E_inside := by
    intro u v huv
    by_cases hv : v < n
    · have hSp := C.spaced u v (by simpa [E,hv] using huv)
      have hn := size_ge n N
      constructor <;> omega
    · have h := (of_decide_eq_true (by simpa [E,hv] using huv) :
        v < size n N ∧ Real n v ∧ u + 1 < v)
      exact ⟨by omega,h.1⟩
  spaced := by
    intro u v huv
    by_cases hv : v < n
    · exact C.spaced u v (by simpa [E,hv] using huv)
    · have h := (of_decide_eq_true (by simpa [E,hv] using huv) :
        v < size n N ∧ Real n v ∧ u + 1 < v)
      exact h.2.2
  downward := by
    intro u v huv w hwu
    by_cases hv : v < n
    · simpa [E,hv] using C.downward u v (by simpa [E,hv] using huv) w hwu
    · have h := (of_decide_eq_true (by simpa [E,hv] using huv) :
        v < size n N ∧ Real n v ∧ u + 1 < v)
      simp only [E,if_neg hv,decide_eq_true_eq]
      exact ⟨h.1,h.2.1,by omega⟩
  linked_E := by
    intro u v huv hu hv hLink
    have hReal : Real n u ∧ Real n v := by
      by_contra hNot
      rcases hLink with ⟨t,ht | ht⟩
      · simp [model,hNot] at ht
      · have hRev : ¬ (Real n v ∧ Real n u) := by tauto
        simp [model,hRev] at ht
    by_cases hLow : v < n
    · have hU : u < n := by omega
      have hLinkC : ∃ t : Fin db,
          C.L.binary u v t = true ∨ C.L.binary v u t = true := by
        rcases hLink with ⟨t,ht | ht⟩
        · refine ⟨t,Or.inl ?_⟩
          simpa [model,hReal.1,hReal.2,project,hU,hLow,
            hSocle u v hU hLow t] using ht
        · refine ⟨t,Or.inr ?_⟩
          simpa [model,hReal.1,hReal.2,project,hU,hLow,
            hSocle v u hLow hU t] using ht
      simpa [E,hLow] using C.linked_E u v huv (by omega) (by omega) hLinkC
    · simp only [E,if_neg hLow,decide_eq_true_eq]
      exact ⟨hv,hReal.2,upper_spacing n u v hReal.1 hReal.2 (by omega) huv⟩

/-- The L-reduct of the actual E-expansion is exactly non-edge padding. -/
theorem partial_preserves_avoidance {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (hn : n ≤ N) (hCarrier : ∀ x, x ∈ A.carrier ↔ x < N)
    (bad : NormalizedForbidden db du dd) (hAvoid : bad.Avoids A) :
    bad.Avoids (partialStructure C A n N hC hSocle).L :=
  preserves_avoidance A n N hn hCarrier bad hAvoid

/-- The padded witness leaves the entire initial auxiliary E-socle unchanged. -/
theorem partial_E_socle {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (u v : Nat) (hv : v < n) :
    (partialStructure C A n N hC hSocle).E u v = C.E u v := by
  simp [partialStructure,E,hv]

/-- Every real upper vertex has all E-links to the retained initial
socle; hence its type over that socle is available before applying F. -/
theorem partial_upper_full_socle {db du dd : Nat}
    (C : EnumeratedPartialStructure db du dd)
    (A : AgeTestModel db du dd) (n N : Nat)
    (hC : n ≤ C.size)
    (hSocle : ∀ x y, x < n → y < n → ∀ t : Fin db,
      A.binary x y t = C.L.binary x y t)
    (i u : Nat) (hi : i < N) (hni : n ≤ i) (hu : u < n) :
    (partialStructure C A n N hC hSocle).E u (address n i) = true := by
  have hAddr : n < address n i := by
    unfold address
    split_ifs <;> omega
  have hSpace : u + 1 < address n i := by
    unfold address
    split_ifs <;> omega
  simp only [partialStructure,E,if_neg (by omega : ¬ address n i < n),decide_eq_true_eq]
  exact ⟨address_lt_size n N i hi,address_real n i,hSpace⟩

end NonedgePadding
end SuccessorTree.V10
