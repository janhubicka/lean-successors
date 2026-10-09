import Mathlib.Tactic

/-!
# Free levels from the literal E axioms of Definition 6.28

The auxiliary binary relation E in a partial structure obeys:
* spacing: E(u,v) implies u < v-1, equivalently u+1 < v;
* downward closure: E(u,v) implies E(w,v) for all w<u.

These two axioms alone imply that, for every vertex v, there is a
UNIQUE cut c such that E(u,v) holds exactly for u<c. The cut is the
paper's free level fl(v) = min{u : not E(u,v)}.

Crucially, the existence and uniqueness of this cut are THEOREMS,
not a new axiom of the partial-type representation. The third
partial-structure axiom (each irreducible pair is E-linked) is
independent and will be used when linking E to the L-structure.
-/

namespace SuccessorTree.V10

/-- Definition 6.28(1), with the Nat subtraction removed. -/
def SpacedE (E : Nat → Nat → Bool) : Prop :=
  ∀ u v, E u v = true → u + 1 < v

/-- Definition 6.28(2): each column of E is downward closed. -/
def DownwardE (E : Nat → Nat → Bool) : Prop :=
  ∀ u v, E u v = true → ∀ w < u, E w v = true

/-- c is the first missing E coordinate of vertex v. -/
def IsFreeCut (E : Nat → Nat → Bool) (v c : Nat) : Prop :=
  (∀ u < c, E u v = true) ∧ E c v = false

/-- A downward-closed E-column cannot resume after its first gap. -/
theorem e_iff_lt_freeCut
    (E : Nat → Nat → Bool) (hDown : DownwardE E)
    (v c : Nat) (hCut : IsFreeCut E v c) (u : Nat) :
    E u v = true ↔ u < c := by
  constructor
  · intro heu
    by_contra hn
    have hle : c ≤ u := by omega
    by_cases heq : u = c
    · subst u
      simp [hCut.2] at heu
    · have hlt : c < u := by omega
      have hc := hDown u v heu c hlt
      simp [hCut.2] at hc
  · intro hlt
    exact hCut.1 u hlt

/-- There is at most one cut that is the first missing E coordinate.
The downward axiom is not needed for this uniqueness direction. -/
theorem freeCut_unique
    (E : Nat → Nat → Bool) (v c d : Nat)
    (hc : IsFreeCut E v c) (hd : IsFreeCut E v d) :
    c = d := by
  by_contra hne
  have hlt : c < d ∨ d < c := by omega
  rcases hlt with hcd | hdc
  · have htrue := hd.1 c hcd
    simp [hc.2] at htrue
  · have htrue := hc.1 d hdc
    simp [hd.2] at htrue

/-- Construct the first missing E coordinate by induction down from
any missing coordinate n. No choice or additional well-ordering axiom
is hidden in this existence proof. -/
private theorem exists_freeCut_of_missing
    (E : Nat → Nat → Bool) (hDown : DownwardE E)
    (v : Nat) :
    ∀ n : Nat, E n v = false →
      ∃ c : Nat, c ≤ n ∧ IsFreeCut E v c := by
  intro n
  induction n with
  | zero =>
      intro hn
      refine ⟨0, le_rfl, ?_⟩
      constructor
      · intro u hu
        omega
      · exact hn
  | succ n ih =>
      intro hn
      by_cases hprev : E n v = false
      · obtain ⟨c, hc, hCut⟩ := ih hprev
        exact ⟨c, Nat.le_succ_of_le hc, hCut⟩
      · have htrue : E n v = true := by
          cases h : E n v with
          | false => exact False.elim (hprev h)
          | true => rfl
        refine ⟨n + 1, le_rfl, ?_⟩
        constructor
        · intro u hu
          by_cases heq : u = n
          · simpa [heq] using htrue
          · have hlt : u < n := by omega
            exact hDown n v htrue u hlt
        · exact hn

/-- Spacing supplies a missing coordinate at v itself; downward
closure then produces the exact first free cut at or below v. -/
theorem exists_freeCut
    (E : Nat → Nat → Bool)
    (hSpace : SpacedE E) (hDown : DownwardE E)
    (v : Nat) :
    ∃ c : Nat, IsFreeCut E v c ∧ c ≤ v := by
  have hv : E v v = false := by
    cases h : E v v with
    | false => rfl
    | true =>
        have bad := hSpace v v h
        omega
  obtain ⟨c, hc, hCut⟩ :=
    exists_freeCut_of_missing E hDown v v hv
  exact ⟨c, hCut, hc⟩

/-- The free cut exists uniquely, as required by the paper's use
of the minimum defining fl in Definition 6.28. -/
theorem existsUnique_freeCut
    (E : Nat → Nat → Bool)
    (hSpace : SpacedE E) (hDown : DownwardE E)
    (v : Nat) :
    ∃! c : Nat, IsFreeCut E v c := by
  obtain ⟨c, hc, _⟩ := exists_freeCut E hSpace hDown v
  exact ⟨c, hc, fun d hd => freeCut_unique E v d c hd hc⟩

/-- The canonical free level is uniquely determined by E; this is
only a choice of the unique object proved above. -/
noncomputable def canonicalFreeLevel
    (E : Nat → Nat → Bool)
    (hSpace : SpacedE E) (hDown : DownwardE E)
    (v : Nat) : Nat :=
  Classical.choose (exists_freeCut E hSpace hDown v)

/-- The chosen canonical free level really is the first E gap. -/
theorem canonicalFreeLevel_isFreeCut
    (E : Nat → Nat → Bool)
    (hSpace : SpacedE E) (hDown : DownwardE E)
    (v : Nat) :
    IsFreeCut E v (canonicalFreeLevel E hSpace hDown v) :=
  (Classical.choose_spec (exists_freeCut E hSpace hDown v)).1

/-- The canonical free level never exceeds its vertex. -/
theorem canonicalFreeLevel_le
    (E : Nat → Nat → Bool)
    (hSpace : SpacedE E) (hDown : DownwardE E)
    (v : Nat) :
    canonicalFreeLevel E hSpace hDown v ≤ v :=
  (Classical.choose_spec (exists_freeCut E hSpace hDown v)).2

/-- All E-incidences with v are exactly its initial free socle. -/
theorem e_iff_lt_canonicalFreeLevel
    (E : Nat → Nat → Bool)
    (hSpace : SpacedE E) (hDown : DownwardE E)
    (u v : Nat) :
    E u v = true ↔ u < canonicalFreeLevel E hSpace hDown v :=
  e_iff_lt_freeCut E hDown v
    (canonicalFreeLevel E hSpace hDown v)
    (canonicalFreeLevel_isFreeCut E hSpace hDown v) u

end SuccessorTree.V10
