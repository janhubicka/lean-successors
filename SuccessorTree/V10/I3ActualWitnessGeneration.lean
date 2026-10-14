import SuccessorTree.V10.I3ActualProperCut
import SuccessorTree.V10.I3FullForbiddenRelocation
import SuccessorTree.V10.I3CrossingAtoms
import Mathlib.Tactic

/-!
# Lemma 6.53: complete generation conclusions from an actual I3 witness

After the finite L-only B3 failure produces an induced forbidden
copy crossing ell, the old proof has three geometric claims:
  (1) upper originals have genuine numerical H coordinates;
  (2) lower vertices have coherent H coordinates and rank bounds;
  (3) the last lower generation is its index r-1 and every upper
      original has generation greater than r-1.

The first follows from irreducibility, complete original L-crossing
types and the exact numerical H generator theorem: no separate
assumption that an upper original is real is needed. For r>=2, the
lower coordinates/rank come from the already checked irreducible
lower-copy theorem. For r=1, the required real coordinate of ell
follows from its positive link to one upper original. Apply the
full induced forbidden-copy relocation contradiction to obtain the
last lower rank; the H top-tie cannot occur because r-1<k, giving
strictly higher upper generations.

The witness must still come from the manuscript's actual I3
prescription and ambient original pool. The separate source function
identity and finite selected-level induction are not assumed here.
No weakened axioms, auxiliary E expansion on W or higher arity.
-/

namespace SuccessorTree.V10

/-- Every upper vertex of an actual irreducible forbidden copy
realizes a named ambient original. Since ell belongs to its lower
part, irreducibility makes this original linked to ell. The exact H
generator theorem proves that its numeric address is a REAL H
coordinate with generation at most k. The real-coordinate premise
in the earlier relocation theorem is therefore a consequence. -/
theorem i3_upper_originals_are_numeric_of_irreducible
    {db du dd t : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 0 < r) (hrt : r < t)
    (W : AgeTestModel db du dd)
    (P : ForbiddenAtomicPattern t db du dd)
    (hIrred : P.Irreducible)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hLast : e (⟨r-1, by omega⟩ : Fin t) = ell)
    (hUpperNamed : ∀ b : Fin t, r ≤ b.val →
      ∃ original : Nat, ell < original ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) original) :
    ∀ b : Fin t, r ≤ b.val →
      ∃ j m : Nat, m ≤ k ∧ ell < hPosition k j m ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (hPosition k j m) := by
  intro b hb
  obtain ⟨original,hAfter,hType⟩ := hUpperNamed b hb
  let last : Fin t := ⟨r-1, by omega⟩
  have hne : last ≠ b := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [last] at hval
    omega
  have hLink : ∃ bit : Fin db,
      W.binary ell (e b) bit = true ∨
      W.binary (e b) ell bit = true := by
    obtain ⟨bit,hP⟩ := hIrred last b hne
    refine ⟨bit,?_⟩
    rcases hP with hP | hP
    · have hEq := hCopy.2.2.1 last b hne bit
      rw [hLast] at hEq
      exact Or.inl (hEq.trans hP)
    · have hEq := hCopy.2.2.1 b last hne.symm bit
      rw [hLast] at hEq
      exact Or.inr (hEq.trans hP)
  obtain ⟨i,j,q,m,hij,hq,hm,hgate,hEll,hOriginal⟩ :=
    i3_named_upper_link_numeric_generators
      K k N ell W (e b) original hAfter hType hLink
  refine ⟨j,m,hm,?_,?_⟩
  · rw [←hOriginal]
    exact hAfter
  · rw [←hOriginal]
    exact hType

/-- Coherent lower real H coordinates and generation-rank bounds
are forced by the ACTUAL ordered irreducible forbidden copy. When
r>=2 use links between distinct lower vertices; for r=1 use the
positive link from ell to a named upper original.

In particular no arbitrary per-lower-vertex real-coordinate
hypothesis remains in the final geometric theorem. -/
theorem i3_lower_numeric_rank_of_irreducible_copy
    {db du dd t : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 0 < r) (hrt : r < t)
    (hrk : r ≤ k)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (P : ForbiddenAtomicPattern t db du dd)
    (hIrred : P.Irreducible)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hLast : e (⟨r-1, by omega⟩ : Fin t) = ell)
    (hUpper : ∀ b : Fin t, r ≤ b.val →
      ∃ j m : Nat, m ≤ k ∧ ell < hPosition k j m ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) (hPosition k j m)) :
    ∃ (first generation : Fin r → Nat),
      (∀ a : Fin r, generation a ≤ k ∧
        e (⟨a.val, Nat.lt_trans a.isLt hrt⟩ : Fin t) =
          hPosition k (first a) (generation a)) ∧
      StrictMono first ∧
      (∀ a : Fin r, a.val ≤ generation a) := by
  classical
  by_cases hOne : r = 1
  · let b : Fin t := ⟨r,hrt⟩
    obtain ⟨j,m,hm,hOrigAfter,hType⟩ := hUpper b (by
      dsimp [b]
      omega)
    let last : Fin t := ⟨r-1, by omega⟩
    have hne : last ≠ b := by
      intro eq
      have hv := congrArg Fin.val eq
      dsimp [last,b] at hv
      omega
    have hLink : ∃ bit : Fin db,
        W.binary ell (e b) bit = true ∨
        W.binary (e b) ell bit = true := by
      obtain ⟨bit,hP⟩ := hIrred last b hne
      refine ⟨bit,?_⟩
      rcases hP with hP | hP
      · have hEq := hCopy.2.2.1 last b hne bit
        rw [hLast] at hEq
        exact Or.inl (hEq.trans hP)
      · have hEq := hCopy.2.2.1 b last hne.symm bit
        rw [hLast] at hEq
        exact Or.inr (hEq.trans hP)
    obtain ⟨i,j',q,m',hij,hq,hm',hgate,hEll,hOriginal⟩ :=
      i3_named_upper_link_numeric_generators
        K k N ell W (e b) (hPosition k j m)
        hOrigAfter hType hLink
    let first : Fin r → Nat := fun _ => i
    let generation : Fin r → Nat := fun _ => q
    have hRep : ∀ a : Fin r, generation a ≤ k ∧
        e (⟨a.val, Nat.lt_trans a.isLt hrt⟩ : Fin t) =
          hPosition k (first a) (generation a) := by
      intro a
      have ha : a.val = 0 := by
        have hlt := a.isLt
        omega
      have hIdx :
          (⟨a.val, Nat.lt_trans a.isLt hrt⟩ : Fin t) = last :=
        Fin.ext (by dsimp [last]; omega)
      refine ⟨hq,?_⟩
      change e (⟨a.val, Nat.lt_trans a.isLt hrt⟩ : Fin t) =
        hPosition k i q
      rw [hIdx]
      exact hLast.trans hEll
    have hFirst : StrictMono first := by
      intro a b hab
      have ha := a.isLt
      have hb := b.isLt
      have hlt := Fin.lt_def.mp hab
      exact False.elim (by omega)
    have hRank : ∀ a : Fin r, a.val ≤ generation a := by
      intro a
      change a.val ≤ q
      have ha := a.isLt
      omega
    exact ⟨first,generation,hRep,hFirst,hRank⟩
  · have hTwo : 2 ≤ r := by omega
    have hBelow : ∀ a : Fin r,
        e (⟨a.val, Nat.lt_trans a.isLt hrt⟩ : Fin t) ≤ ell := by
      intro a
      let lo : Fin t := ⟨a.val, Nat.lt_trans a.isLt hrt⟩
      let last : Fin t := ⟨r-1, by omega⟩
      have hle : lo ≤ last := Fin.le_def.mpr (by
        dsimp [lo,last]
        have ha := a.isLt
        omega)
      change e lo ≤ ell
      calc
        e lo ≤ e last := hCopy.1.monotone hle
        _ = ell := hLast
    exact i3_forbidden_lower_real_generation_rank
      K k N ell r hTwo (Nat.le_of_lt hrt)
      (by omega : r ≤ k+1) W hSocle
      P hIrred e hCopy hBelow

/-- This is the geometric generation conclusion of Lemma 6.53,
given only an ACTUAL finite L-age witness with common numerical H
socle, the proper cut and complete ambient original labels ABOVE
that cut. No manual real-coordinate, rank, admissible-generation-
gate or relocation-homomorphism hypothesis is assumed.

The full relocation contradiction proves the last lower generation
equals r-1; irreducibility at ell then forces every named upper
original to have generation strictly greater than r-1.
The remaining paper-specific task is to derive these actual finite
witness data from the exact I3 selected-stage prescription. -/
theorem numericI3_actual_witness_generation_conclusions
    {db du dd t : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 0 < r) (hrt : r < t)
    (hrk : r ≤ k)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (P : ForbiddenAtomicPattern t db du dd)
    (hIrred : P.Irreducible)
    (e : Fin t → Nat) (hCopy : W.Realizes P e)
    (hDelete : ¬ ∃ f : Fin t → Nat,
      (W.withoutVertex ell).Realizes P f)
    (hLast : e (⟨r-1, by omega⟩ : Fin t) = ell)
    (hUpperNamed : ∀ b : Fin t, r ≤ b.val →
      ∃ original : Nat, ell < original ∧
        RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
          RelationalPrefixType.ofAgeModel
            (finiteNumericHL K k N) (ell+1) original) :
    ∃ i : Nat,
      ell = hPosition k i (r-1) ∧
      (∀ b : Fin t, r ≤ b.val →
        ∃ j m : Nat, r-1 < m ∧ m ≤ k ∧
          ell < hPosition k j m ∧
          RelationalPrefixType.ofAgeModel W (ell+1) (e b) =
            RelationalPrefixType.ofAgeModel
              (finiteNumericHL K k N) (ell+1)
              (hPosition k j m)) := by
  classical
  have hUpper :=
    i3_upper_originals_are_numeric_of_irreducible
      K k N ell r hr hrt W P hIrred e hCopy hLast hUpperNamed
  obtain ⟨first,generation,hRep,hFirst,hRank⟩ :=
    i3_lower_numeric_rank_of_irreducible_copy
      K k N ell r hr hrt hrk W hSocle
      P hIrred e hCopy hLast hUpper
  have hGenLast :
      generation ⟨r-1, by omega⟩ = r-1 :=
    numericI3_forbidden_copy_forces_last_lower_rank
      K k N ell r hr hrt hrk W hSocle
      P hIrred e hCopy hDelete
      first generation hFirst hRep hRank hLast hUpper
  let last : Fin r := ⟨r-1, by omega⟩
  let loLast : Fin t := ⟨r-1, by omega⟩
  have hTestedPos :
      ell = hPosition k (first last) (r-1) := by
    have hRepLast := (hRep last).2
    have hLastAt : e loLast = ell := hLast
    change e loLast =
      hPosition k (first last) (generation last) at hRepLast
    rw [hGenLast] at hRepLast
    exact hLastAt.symm.trans hRepLast
  have hNonTop : r-1 < k := by omega
  refine ⟨first last,hTestedPos,?_⟩
  intro b hb
  obtain ⟨j,m,hm,hOrigAfter,hType⟩ := hUpper b hb
  have hNE : loLast ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [loLast] at hv
    omega
  have hLink : ∃ bit : Fin db,
      W.binary ell (e b) bit = true ∨
      W.binary (e b) ell bit = true := by
    obtain ⟨bit,hP⟩ := hIrred loLast b hNE
    refine ⟨bit,?_⟩
    rcases hP with hP | hP
    · have hEq := hCopy.2.2.1 loLast b hNE bit
      rw [hLast] at hEq
      exact Or.inl (hEq.trans hP)
    · have hEq := hCopy.2.2.1 b loLast hNE.symm bit
      rw [hLast] at hEq
      exact Or.inr (hEq.trans hP)
  have hHigher : r-1 < m :=
    i3_named_upper_generation_strict_of_nonTop_tested
      K k N ell W (e b) (hPosition k j m)
      hOrigAfter hType hLink
      (first last) j (r-1) m
      hTestedPos rfl hNonTop hm
  exact ⟨j,m,hHigher,hm,hOrigAfter,hType⟩

end SuccessorTree.V10
