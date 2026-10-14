import SuccessorTree.V10.I3ClosureCrossingGraph
import SuccessorTree.V10.PrescribedBoringCompletion
import Mathlib.Tactic

/-!
# I3: a genuinely non-skippable closure crossing fails corrected B3

The actual one-level predecessor map of Algorithm 5.4 must cover
EVERY closure node above the tested cut, not just an arbitrarily
chosen representative of each source type.  When its complete
old/next raw nodes are prescribed, the verified Lemma 6.51
boring-extension construction turns corrected B3 into one
Kpt shape map skipping exactly that cut and agreeing with every
closure crossing.

Consequently a failure of one-level extendability is a failure
of corrected B3, under no separate finite L-witness hypothesis.
The age test remains L-only, without E on an arbitrary finite
forbidden-copy witness.

The remaining algorithm-specific work is to construct the
complete prescribed source from the actual closure and prove that
it covers every crossing.  The no-I2 uniqueness theorem already
exists in the generic envelope algorithm.
-/

namespace SuccessorTree.V10

/-- The stage function f_ell covers each crossing of its actual
closure Z.  This is the FORWARD direction absent from the weaker
IsCrossingGraphOf, which represents every prescribed input by
some closure node but does not guarantee that no closure node
is omitted.  Both directions will hold for the actual Algorithm
5.4 source. -/
def CoversClosureCrossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat)
    (F : PrescribedBoringData ell db du dd) : Prop :=
  ∀ z : AdmissibleKptNode family, z ∈ Z →
    ∀ (hz : ell < LevelTree.lev z),
      ∃ T : PartialTypeWithE ell db du dd,
        T ∈ F.source ∧
        (⟨ell,T⟩ : RawPartialTypeNode db du dd) =
          (LevelTree.ancestor z ell (Nat.le_of_lt hz)).val ∧
        (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) =
          (LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)).val

/-- The concrete monoid cannot skip level ell while respecting
all crossings of this closure.  This is the I3 obstruction,
with no artificial restriction on the finite L-only age test. -/
def NonSkippableClosureCrossing
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat) : Prop :=
  ¬ ∃ Φ : SuccessorTree.ShapeMap (admissibleKptSTree family),
    Φ ∈ KptM family ∧ Φ.SkipsOnly ell ∧
    ∀ z : AdmissibleKptNode family, z ∈ Z →
      ∀ (hz : ell < LevelTree.lev z),
        Φ (LevelTree.ancestor z ell (Nat.le_of_lt hz)) =
          LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)

/-- The author's I3 deduction from Lemma 6.51, now using the
ACTUAL complete selected closure crossing graph.

B1/B2 are built into F.  The only further hypotheses of the
one-gap theorem are that every actual prescribed target is
admissible and the inserted level is positive.  Thus a
non-skippable level must fail corrected B3. -/
theorem nonSkippableClosureCrossing_implies_failedCorrectedB3
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (Z : Set (AdmissibleKptNode family))
    (ell : Nat) (hPos : 0 < ell)
    (F : PrescribedBoringData ell db du dd)
    (hCover : CoversClosureCrossing family Z ell F)
    (hTargets : ∀ S, S ∈ F.source →
      IsAdmissibleRawType family
        (⟨ell+1,F.target S⟩ : RawPartialTypeNode db du dd))
    (hNoSkip : NonSkippableClosureCrossing family Z ell) :
    ¬ F.CorrectedB3 family := by
  intro hB3
  obtain ⟨Φ,hMem,hSkip,hValues⟩ :=
    F.prescribedKpt_boring_extension_exists family hB3 hTargets hPos
  apply hNoSkip
  refine ⟨Φ,hMem,hSkip,?_⟩
  intro z hZ hz
  obtain ⟨T,hSrc,hOldRaw,hNewRaw⟩ := hCover z hZ hz
  let oldNode : AdmissibleKptNode family :=
    LevelTree.ancestor z ell (Nat.le_of_lt hz)
  let nextNode : AdmissibleKptNode family :=
    LevelTree.ancestor z (ell+1) (Nat.succ_le_iff.mpr hz)
  have hAdT : IsAdmissibleRawType family
      (⟨ell,T⟩ : RawPartialTypeNode db du dd) := by
    rw [hOldRaw]
    exact oldNode.property
  have hOldNode :
      (⟨⟨ell,T⟩,hAdT⟩ : AdmissibleKptNode family) = oldNode :=
    Subtype.ext hOldRaw
  have hMapVal :
      (Φ (⟨⟨ell,T⟩,hAdT⟩ : AdmissibleKptNode family)).val =
        (⟨ell+1,F.target T⟩ : RawPartialTypeNode db du dd) :=
    hValues T hSrc hAdT
  apply Subtype.ext
  change (Φ oldNode).val = nextNode.val
  rw [←hOldNode]
  exact hMapVal.trans hNewRaw

end SuccessorTree.V10
