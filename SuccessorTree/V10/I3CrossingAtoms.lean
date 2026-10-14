import SuccessorTree.V10.HFinitePartial
import SuccessorTree.V10.HGenerationRank
import SuccessorTree.V10.RelationalTypeReduct
import SuccessorTree.V10.ChosenAgeSignatures
import Mathlib.Tactic

/-!
# Full directed crossing records of a named I3 upper original

In Lemma 6.53 the lower forbidden-copy vertices are moved inside
the common initial L-socle of the age witness, but the upper
vertices stay fixed. For the lower--upper zone, one needs equality
of BOTH directed binary relations to a chosen ambient original
through the entire tested cut, not merely one positive edge.

The complete induced L-type already contains exactly these bits.
The lemmas here project the source's full original-name equality
to all incident atoms and singleton facts. This gives a small,
kernel-checkable bridge from Observation 6.52 to the mixed
relocation argument without introducing E in the age witness.

The final numeric H-generation relocation remains separate. No
axioms or definitions of the successor manuscript are changed.
-/

namespace SuccessorTree.V10

/-- Equality of complete finite L-types determines every directed
edge, nonedge and loop between the distinguished upper vertex and
the initial socle, plus all unary and diagonal facts of that upper
vertex. The same argument works even if the old upper address is
outside the socle: `none` is the distinguished type vertex. -/
theorem fullOriginalType_all_incident_atoms
    {db du dd : Nat}
    (W C : AgeTestModel db du dd)
    (cut upper original : Nat)
    (hType :
      RelationalPrefixType.ofAgeModel W cut upper =
        RelationalPrefixType.ofAgeModel C cut original) :
    (∀ (x : Nat), x < cut → ∀ t : Fin db,
      W.binary x upper t = C.binary x original t ∧
      W.binary upper x t = C.binary original x t) ∧
    (∀ t : Fin db, W.binary upper upper t =
      C.binary original original t) ∧
    (∀ t : Fin du, W.unary upper t = C.unary original t) ∧
    (∀ t : Fin dd, W.diagonal upper t = C.diagonal original t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx t
    let ix : Fin cut := ⟨x, hx⟩
    have hForward := congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.binary (some ix) none t) hType
    have hBackward := congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.binary none (some ix) t) hType
    exact ⟨hForward, hBackward⟩
  · intro t
    exact congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.binary none none t) hType
  · intro t
    exact congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.unary none t) hType
  · intro t
    exact congrArg
      (fun T : RelationalPrefixType cut db du dd =>
        T.diagonal none t) hType

/-- An actual original name for an upper I3 witness vertex supplies
every incident atom through the tested coordinate ell. In particular,
`x=ell` is included: the named original controls the relation to
the new tested vertex itself, which is essential for Lemma 6.53. -/
theorem chosenAgeSignature_some_incident_atoms
    {r M db du dd : Nat}
    (C W : AgeTestModel db du dd)
    (original : Fin M → Nat)
    (ell : Nat) (e : Fin r → Nat)
    (hOriginal : ∀ a : Fin r, ell < e a →
      ∃ v : Fin M,
        RelationalPrefixType.ofAgeModel W (ell + 1) (e a) =
          RelationalPrefixType.ofAgeModel C (ell + 1) (original v))
    (a : Fin r) (v : Fin M)
    (hSome : chosenAgeSignature C W original ell e hOriginal a = some v) :
    (∀ x, x ≤ ell → ∀ t : Fin db,
      W.binary x (e a) t = C.binary x (original v) t ∧
      W.binary (e a) x t = C.binary (original v) x t) ∧
    (∀ t : Fin db, W.binary (e a) (e a) t =
      C.binary (original v) (original v) t) ∧
    (∀ t : Fin du, W.unary (e a) t =
      C.unary (original v) t) ∧
    (∀ t : Fin dd, W.diagonal (e a) t =
      C.diagonal (original v) t) := by
  have hType := chosenAgeSignature_some_type
    C W original ell e hOriginal a v hSome
  simpa only [Nat.lt_succ_iff] using
    fullOriginalType_all_incident_atoms
      W C (ell + 1) (e a) (original v) hType

/-- A positive directed relation between two LOWER vertices of
an actual I3 finite L-only witness forces both vertices to be real
numerical H vertices. Their first indices are strictly increasing,
and their generations satisfy precisely the existing H gate.

This is derived from literal agreement of the initial L-socle with
the finite H construction; no abstract real-vertex/linked-pair
assumption enters this statement. -/
theorem i3_linked_lower_pair_numeric_generators
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N ell : Nat)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (x y : Nat) (hxy : x < y) (hy : y ≤ ell)
    (hLink : ∃ t : Fin db,
      W.binary x y t = true ∨ W.binary y x t = true) :
    ∃ i j q m : Nat,
      i < j ∧ q ≤ k ∧ m ≤ k ∧
      (q < m ∨ (q = m ∧ m = k)) ∧
      x = hPosition k i q ∧ y = hPosition k j m := by
  have hx : x ≤ ell := Nat.le_trans (Nat.le_of_lt hxy) hy
  have hCopyXY : ∀ t : Fin db,
      W.binary x y t = hNumericBinary K.binary k x y t := by
    intro t
    exact hSocle.2.1 x y hx hy t
  have hCopyYX : ∀ t : Fin db,
      W.binary y x t = hNumericBinary K.binary k y x t := by
    intro t
    exact hSocle.2.1 y x hy hx t
  obtain ⟨t,ht⟩ := hLink
  have hRealLink : ∃ t : Fin db,
      hNumericBinary K.binary k x y t = true ∨
      hNumericBinary K.binary k y x t = true := by
    refine ⟨t,?_⟩
    rcases ht with ht | ht
    · exact Or.inl ((hCopyXY t).symm.trans ht)
    · exact Or.inr ((hCopyYX t).symm.trans ht)
  exact hNumericBinary_linked_generators K.binary k x y
    hxy hRealLink

/-- If the I3 witness has a positive relation between its TESTED
coordinate ell and a named upper original, then the complete upper
type identifies ell and that original as linked, real H vertices,
with ordered base first indices and the permitted generation gate.

The hypothesis ell < original is the genuine crossing guard; it
will follow from the manuscript's free-level cut for the actual
chosen original pool. In contrast, it need not hold for an
arbitrary unguarded source list. -/
theorem i3_named_upper_link_numeric_generators
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N ell : Nat)
    (W : AgeTestModel db du dd)
    (w original : Nat) (hOrder : ell < original)
    (hType :
      RelationalPrefixType.ofAgeModel W (ell+1) w =
        RelationalPrefixType.ofAgeModel
          (finiteNumericHL K k N) (ell+1) original)
    (hLink : ∃ t : Fin db,
      W.binary ell w t = true ∨ W.binary w ell t = true) :
    ∃ i j q m : Nat,
      i < j ∧ q ≤ k ∧ m ≤ k ∧
      (q < m ∨ (q = m ∧ m = k)) ∧
      ell = hPosition k i q ∧
      original = hPosition k j m := by
  have hCross :=
    (fullOriginalType_all_incident_atoms W
      (finiteNumericHL K k N) (ell+1) w original hType).1
      ell (Nat.lt_succ_self ell)
  obtain ⟨t,ht⟩ := hLink
  have hRealLink : ∃ t : Fin db,
      hNumericBinary K.binary k ell original t = true ∨
      hNumericBinary K.binary k original ell t = true := by
    refine ⟨t,?_⟩
    rcases ht with ht | ht
    · exact Or.inl ((hCross t).1.symm.trans ht)
    · exact Or.inr ((hCross t).2.symm.trans ht)
  exact hNumericBinary_linked_generators K.binary k ell original
    hOrder hRealLink


/-- The lower part of an actual irreducible I3 forbidden copy,
once it has at least TWO vertices, consists of consistently labelled
real numerical H vertices. Their first indices are strictly increasing,
their generations satisfy the exact linked-pair gate, and the a-th
generation is at least a.

This assembles the *same* real-coordinate representations for every
pair, using injectivity of the bounded numerical H encoding.
The linked-pair premise comes from irreducibility of the actual
induced forbidden configuration; its extraction from that copy is
a separate straightforward interface. The r=1 case is supplied
instead by the named-upper crossing lemma above. -/
theorem i3_lower_irreducible_numeric_rank
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 2 ≤ r) (hrk : r ≤ k+1)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (e : Fin r → Nat) (hOrder : StrictMono e)
    (hBelow : ∀ a : Fin r, e a ≤ ell)
    (hLinked : ∀ a b : Fin r, a < b →
      ∃ t : Fin db,
        W.binary (e a) (e b) t = true ∨
        W.binary (e b) (e a) t = true) :
    ∃ (first generation : Fin r → Nat),
      (∀ a : Fin r, generation a ≤ k ∧
        e a = hPosition k (first a) (generation a)) ∧
      StrictMono first ∧
      (∀ a : Fin r, a.val ≤ generation a) := by
  classical
  have hReal : ∀ a : Fin r,
      ∃ i q : Nat, q ≤ k ∧ e a = hPosition k i q := by
    intro a
    by_cases ha : a.val = 0
    · let b : Fin r := ⟨1, by omega⟩
      have hab : a < b := Fin.lt_def.mpr (by dsimp [b]; omega)
      obtain ⟨i,j,q,m,_hij,hq,_hm,_hgate,hx,_hy⟩ :=
        i3_linked_lower_pair_numeric_generators K k N ell W
          hSocle (e a) (e b) (hOrder hab) (hBelow b)
          (hLinked a b hab)
      exact ⟨i,q,hq,hx⟩
    · let b : Fin r := ⟨0, by omega⟩
      have hba : b < a := Fin.lt_def.mpr (by dsimp [b]; omega)
      obtain ⟨_i,j,_q,m,_hij,_hq,hm,_hgate,_hx,hy⟩ :=
        i3_linked_lower_pair_numeric_generators K k N ell W
          hSocle (e b) (e a) (hOrder hba) (hBelow a)
          (hLinked b a hba)
      exact ⟨j,m,hm,hy⟩
  let first : Fin r → Nat := fun a => Classical.choose (hReal a)
  let generation : Fin r → Nat :=
    fun a => Classical.choose (Classical.choose_spec (hReal a))
  have hRep : ∀ a : Fin r,
      generation a ≤ k ∧
      e a = hPosition k (first a) (generation a) := by
    intro a
    exact Classical.choose_spec (Classical.choose_spec (hReal a))
  have hPairs : ∀ a b : Fin r, a < b →
      first a < first b ∧
      (generation a < generation b ∨
        (generation a = k ∧ generation b = k)) := by
    intro a b hab
    obtain ⟨i,j,q,m,hij,hq,hm,hgate,hx,hy⟩ :=
      i3_linked_lower_pair_numeric_generators K k N ell W
        hSocle (e a) (e b) (hOrder hab) (hBelow b)
        (hLinked a b hab)
    have haEq :
        hPosition k (first a) (generation a) =
          hPosition k i q :=
      (hRep a).2.symm.trans hx
    have hbEq :
        hPosition k (first b) (generation b) =
          hPosition k j m :=
      (hRep b).2.symm.trans hy
    obtain ⟨hi, hqGen⟩ :=
      hPosition_injective_bounded k
        (first a) (generation a) i q (hRep a).1 hq haEq
    obtain ⟨hj, hmGen⟩ :=
      hPosition_injective_bounded k
        (first b) (generation b) j m (hRep b).1 hm hbEq
    constructor
    · omega
    · rcases hgate with hlt | ⟨heq,htop⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, by omega⟩
  refine ⟨first,generation,hRep,?_,?_⟩
  · intro a b hab
    exact (hPairs a b hab).1
  · exact generation_rank_lower_bound k r hrk generation
      (fun a b hab => (hPairs a b hab).2)


/-- Restrict one ACTUAL ordered induced forbidden copy to its
first r vertices. Pairwise irreducibility supplies the positive
directed link between every two distinct lower vertices, not an
extra assumption about the hypothetical age witness. -/
theorem i3_forbidden_copy_lower_links
    {t r db du dd : Nat}
    (P : ForbiddenAtomicPattern t db du dd) (hIrred : P.Irreducible)
    (W : AgeTestModel db du dd)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hr : r ≤ t)
    (a b : Fin r) (hab : a < b) :
    ∃ u : Fin db,
      W.binary (e ⟨a.val, lt_of_lt_of_le a.isLt hr⟩)
          (e ⟨b.val, lt_of_lt_of_le b.isLt hr⟩) u = true ∨
      W.binary (e ⟨b.val, lt_of_lt_of_le b.isLt hr⟩)
          (e ⟨a.val, lt_of_lt_of_le a.isLt hr⟩) u = true := by
  let aa : Fin t := ⟨a.val, lt_of_lt_of_le a.isLt hr⟩
  let bb : Fin t := ⟨b.val, lt_of_lt_of_le b.isLt hr⟩
  have hne : aa ≠ bb := by
    intro h
    have hv := congrArg Fin.val h
    exact (Nat.ne_of_lt (Fin.lt_def.mp hab)) hv
  obtain ⟨u,hLink⟩ := hIrred aa bb hne
  refine ⟨u,?_⟩
  rcases hLink with hAB | hBA
  · exact Or.inl ((hCopy.2.2.1 aa bb hne u).trans hAB)
  · exact Or.inr ((hCopy.2.2.1 bb aa hne.symm u).trans hBA)

/-- For an actual irreducible induced forbidden copy, the initial
r≥2 vertices lying in the exact H socle admit coherent real
coordinates with increasing original first indices and generation
at least their ordinal rank.

This is the first half of Lemma 6.53 without assuming an
abstract linked configuration. The remaining cases are r=1
(using the tested-level/upper-original relation), and the
relocation-to-forbidden-age contradiction that forces the final
lower generation to equal r-1. -/
theorem i3_forbidden_lower_real_generation_rank
    {db du dd t : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 2 ≤ r)
    (hrt : r ≤ t) (hrk : r ≤ k+1)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (P : ForbiddenAtomicPattern t db du dd)
    (hIrred : P.Irreducible)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hBelow : ∀ a : Fin r,
      e ⟨a.val, lt_of_lt_of_le a.isLt hrt⟩ ≤ ell) :
    ∃ (first generation : Fin r → Nat),
      (∀ a : Fin r, generation a ≤ k ∧
        e ⟨a.val, lt_of_lt_of_le a.isLt hrt⟩ =
          hPosition k (first a) (generation a)) ∧
      StrictMono first ∧
      (∀ a : Fin r, a.val ≤ generation a) := by
  let eLower : Fin r → Nat := fun a =>
    e ⟨a.val, lt_of_lt_of_le a.isLt hrt⟩
  have hOrder : StrictMono eLower := by
    intro a b hab
    exact hCopy.1 (Fin.lt_def.mpr (Fin.lt_def.mp hab))
  have hLinked : ∀ a b : Fin r, a < b →
      ∃ u : Fin db,
        W.binary (eLower a) (eLower b) u = true ∨
        W.binary (eLower b) (eLower a) u = true := by
    intro a b hab
    exact i3_forbidden_copy_lower_links P hIrred W e hCopy hrt a b hab
  exact i3_lower_irreducible_numeric_rank
    K k N ell r hr hrk W hSocle eLower hOrder hBelow hLinked


end SuccessorTree.V10
