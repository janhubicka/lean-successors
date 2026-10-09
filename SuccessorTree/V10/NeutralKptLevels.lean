import SuccessorTree.V10.RootFixingMonoidM1
import SuccessorTree.V10.AdmissibleKptPrefix
import Mathlib.Tactic

/-!
# Explicit nodes on every level of the normalized Kpt forest

M3 in Section 6.3.2 forces all levels of any (S,M)-tree to be
inhabited.  This is an important nonemptiness check when attempting
to instantiate the abstract monoid axioms for the concrete tree.

We independently construct a vertex of every level in the normalized
Kpt family: take an entirely empty L-structure on vertices
0,...,n+1, and give the distinguished last vertex n+1 precisely the
E-socle {0,...,n-1}. The intervening coordinate n is a neutral
filler, required by E spacing.

The normalized forbidden family cannot occur in this structure:
all nontrivial forbidden patterns are irreducible and therefore
have a positive binary atom, and forbidden singletons are
non-neutral. The absence of a forbidden empty structure is
encoded by NormalizedForbidden itself.

This proves nonemptiness for all levels WITHOUT assuming M3.
It does NOT construct the duplication maps demanded by M3.
-/

namespace SuccessorTree.V10

/-- The empty L-reduct on n+2 ordered ordinary vertices. -/
def neutralKptL (db du dd n : Nat) :
    AgeTestModel db du dd :=
  { carrier := {v | v < n + 2}
    binary := fun _ _ _ => false
    unary := fun _ _ => false
    diagonal := fun _ _ => false }

/-- A single E-column, at vertex n+1, with free cut exactly n. -/
def neutralKptE (n u v : Nat) : Bool :=
  decide (v = n + 1 ∧ u < n)

/-- The neutral structure satisfies all three literal partial
structure E axioms, with the E3 condition vacuous because L is
entirely empty. -/
def neutralKptPartialStructure (db du dd n : Nat) :
    EnumeratedPartialStructure db du dd := by
  refine
    { size := n + 2
      L := neutralKptL db du dd n
      carrier_iff := ?_
      E := neutralKptE n
      E_inside := ?_
      spaced := ?_
      downward := ?_
      linked_E := ?_ }
  · intro v
    rfl
  · intro u v he
    have h : v = n + 1 ∧ u < n := by
      simpa [neutralKptE] using he
    constructor <;> omega
  · intro u v he
    have h : v = n + 1 ∧ u < n := by
      simpa [neutralKptE] using he
    omega
  · intro u v he w hw
    have h : v = n + 1 ∧ u < n := by
      simpa [neutralKptE] using he
    apply (show neutralKptE n w v = true from ?_)
    simp [neutralKptE, h.1, lt_trans hw h.2]
  · intro u v huv hu hv hlink
    obtain ⟨r, hr⟩ := hlink
    simp [neutralKptL] at hr

/-- The last vertex in the neutral structure has free level n,
including at n=0. -/
theorem neutralKpt_freeLevel (db du dd n : Nat) :
    (neutralKptPartialStructure db du dd n).freeLevel (n + 1) = n := by
  have hCut : IsFreeCut (neutralKptE n) (n + 1) n := by
    constructor
    · intro u hu
      simp [neutralKptE, hu]
    · simp [neutralKptE]
  exact freeCut_unique (neutralKptE n) (n + 1)
    ((neutralKptPartialStructure db du dd n).freeLevel (n + 1))
    n
    (canonicalFreeLevel_isFreeCut (neutralKptE n)
      (neutralKptPartialStructure db du dd n).spaced
      (neutralKptPartialStructure db du dd n).downward
      (n + 1))
    hCut

/-- A normalized forbidden configuration cannot be induced in an
entirely empty binary/unary/diagonal relational structure. -/
theorem neutralKpt_avoids
    {db du dd : Nat}
    (bad : NormalizedForbidden db du dd) (n : Nat) :
    bad.Avoids (neutralKptL db du dd n) := by
  cases bad with
  | singleton F hNonNeutral =>
    rintro ⟨f, hCopy⟩
    rcases hNonNeutral with ⟨r, hR⟩ | ⟨r, hR⟩
    · have hp := hCopy.2.2.2.1 0 r
      have hfalse : (neutralKptL db du dd n).unary (f 0) r =
          false := rfl
      rw [hfalse, hR] at hp
      contradiction
    · have hp := hCopy.2.2.2.2 0 r
      have hfalse : (neutralKptL db du dd n).diagonal (f 0) r =
          false := rfl
      rw [hfalse, hR] at hp
      contradiction
  | nontrivial m F hm hirred =>
    rintro ⟨f, hCopy⟩
    let a : Fin m := ⟨0, by omega⟩
    let b : Fin m := ⟨1, hm⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      norm_num [a, b] at hv
    obtain ⟨r, hr⟩ := hirred a b hab
    rcases hr with hr | hr
    · have hp := hCopy.2.2.1 a b hab r
      have hfalse : (neutralKptL db du dd n).binary
          (f a) (f b) r = false := rfl
      rw [hfalse, hr] at hp
      contradiction
    · have hp := hCopy.2.2.1 b a hab.symm r
      have hfalse : (neutralKptL db du dd n).binary
          (f b) (f a) r = false := rfl
      rw [hfalse, hr] at hp
      contradiction

/-- One concrete admissible node at every level of the normalized
Kpt tree. No appeal to M3 or pruning is made. -/
noncomputable def neutralKptNode
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) : AdmissibleKptNode family := by
  let A := neutralKptPartialStructure db du dd n
  let Q := A.partialTypeAt n (n + 1)
  have hAd : IsAdmissibleRawType family
      (⟨n, Q⟩ : RawPartialTypeNode db du dd) := by
    have hAvoid : ∀ bad, bad ∈ family → bad.Avoids A.L := by
      intro bad _
      exact neutralKpt_avoids bad n
    refine ⟨A, n + 1, ?_, hAvoid, ?_⟩
    · change n + 1 < n + 2
      omega
    · change (⟨n, A.partialTypeAt n (n + 1)⟩ :
        RawPartialTypeNode db du dd) =
        (⟨A.freeLevel (n + 1),
          A.partialTypeAt (A.freeLevel (n + 1)) (n + 1)⟩ :
            RawPartialTypeNode db du dd)
      have hCut : A.freeLevel (n + 1) = n :=
        neutralKpt_freeLevel db du dd n
      rw [hCut]
  exact ⟨⟨n, Q⟩, hAd⟩

/-- Unlike for an arbitrary abstract LevelTree, the normalized
forbidden-free Kpt family has an actual node on every level. -/
theorem admissibleKpt_level_nonempty
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (n : Nat) :
    ∃ a : AdmissibleKptNode family, LevelTree.lev a = n := by
  refine ⟨neutralKptNode family n, ?_⟩
  rfl

end SuccessorTree.V10
