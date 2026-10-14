import SuccessorTree.V10.I1RealNodeMeetCharge
import Mathlib.Tactic

/-!
# Proposition 6.44: the actual top-generation seed geometry

The proof starts its envelope with one root original O+ and the
prefixes of O+ through coordinates of the copied A'. In the
numerical H construction these coordinates lie in generation k.

Rather than assuming all seed levels avoid intermediate positive
generations, define the finite seed family literally as one actual
Kpt original plus its ancestors at top-generation real positions.
Then establish (1) every seed is represented by this SAME original,
(2) there are at most q+1 seed nodes for q chosen positions, and
(3) no seed has level iota(p,r) for 0<r<k.

The last fact combines the checked odd-or-zero E-free level of
the root with bounded injectivity of the real H position encoding.
Together with the actual closure normal form and parity theorem,
it eliminates the final seed exception in the I1 meet-charge lemma.
No arbitrary E-relation is introduced on forbidden L-age witnesses.
-/

namespace SuccessorTree.V10

/-- One genuine root original and its prefixes at a FINITE set
of top-generation H coordinates. The displayed bound certifies
that every selected prefix is below that root's actual free cut. -/
noncomputable def numericHTopGenerationSeeds
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val) :
    Finset (AdmissibleKptNode family) := by
  classical
  let root : AdmissibleKptNode family :=
    (finiteNumericH K k N).kptOriginal family hAvoidH c
  let mkPrefix : Subtype (fun i : Nat => i ∈ blocks) → AdmissibleKptNode family :=
    fun i => LevelTree.ancestor root (hPosition k i.val k) (by
      change hPosition k i.val k ≤
        (finiteNumericH K k N).freeLevel c.val
      exact hWithin i.val i.property)
  exact insert root (blocks.attach.image mkPrefix)

/-- Every seed has one of the two literal source forms; none is an
arbitrary same-type representative chosen elsewhere in the ambient. -/
theorem numericHTopGenerationSeeds_cases
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (z : AdmissibleKptNode family)
    (hz : z ∈ numericHTopGenerationSeeds
      family K k N hAvoidH c blocks hWithin) :
    z = (finiteNumericH K k N).kptOriginal family hAvoidH c ∨
      ∃ i : Subtype (fun i : Nat => i ∈ blocks),
        z = LevelTree.ancestor
          ((finiteNumericH K k N).kptOriginal family hAvoidH c)
          (hPosition k i.val k) (hWithin i.val i.property) := by
  classical
  unfold numericHTopGenerationSeeds at hz
  change z ∈ insert
    ((finiteNumericH K k N).kptOriginal family hAvoidH c)
    (blocks.attach.image (fun i : Subtype (fun i : Nat => i ∈ blocks) =>
      LevelTree.ancestor
        ((finiteNumericH K k N).kptOriginal family hAvoidH c)
        (hPosition k i.val k) (hWithin i.val i.property))) at hz
  rcases Finset.mem_insert.mp hz with hroot | hp
  · exact Or.inl hroot
  · obtain ⟨i, _hi, hEq⟩ := Finset.mem_image.mp hp
    exact Or.inr ⟨i, hEq.symm⟩

/-- All seeds are prefixes of the SAME original c. This is the
concrete input for the original-pool closure theorem with U={c}. -/
theorem numericHTopGenerationSeeds_subset_rootPool
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val) :
    (numericHTopGenerationSeeds
      family K k N hAvoidH c blocks hWithin :
      Set (AdmissibleKptNode family)) ⊆
        ambientPrefixPool family (finiteNumericH K k N)
          hAvoidH ({c} : Set (Fin N)) := by
  intro z hz
  have hSingleton : c ∈ ({c} : Set (Fin N)) := by simp
  obtain hRoot | ⟨i,hPrefix⟩ :=
    numericHTopGenerationSeeds_cases
      family K k N hAvoidH c blocks hWithin z hz
  · rw [hRoot]
    exact ⟨_,⟨c,hSingleton,rfl⟩,le_rfl⟩
  · rw [hPrefix]
    exact ⟨_,⟨c,hSingleton,rfl⟩,
      LevelTree.ancestor_le _ _ _⟩

/-- Top-generation real coordinates cannot coincide with real
coordinates in any strictly smaller positive generation. -/
theorem numericHTopLevel_ne_lowerGeneration
    (k i p r : Nat) (hr : r < k) :
    hPosition k i k ≠ hPosition k p r := by
  intro h
  obtain ⟨_,hGen⟩ :=
    hPosition_injective_bounded k i k p r le_rfl
      (Nat.le_of_lt hr) h
  omega

/-- The actual O+ root and all prescribed top-generation prefixes
avoid every intermediate real level. The root's level is the
ACTUAL H free cut, which is either zero or odd. -/
theorem numericHTopGenerationSeeds_noIntermediateReal
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (p r : Nat) (hr : 0 < r) (hrk : r < k) :
    ∀ z ∈ numericHTopGenerationSeeds
      family K k N hAvoidH c blocks hWithin,
      LevelTree.lev z ≠ hPosition k p r := by
  intro z hz
  obtain hRoot | ⟨i,hPrefix⟩ :=
    numericHTopGenerationSeeds_cases
      family K k N hAvoidH c blocks hWithin z hz
  · rw [hRoot]
    change (finiteNumericH K k N).freeLevel c.val ≠ hPosition k p r
    by_cases hFree : (finiteNumericH K k N).freeLevel c.val = 0
    · rw [hFree]
      unfold hPosition
      omega
    · have hPos : 0 < (finiteNumericH K k N).freeLevel c.val := by omega
      exact finiteNumericH_positive_freeLevel_ne_realPosition
        K k N c.val p r c.isLt hPos
  · rw [hPrefix]
    have hLev :
        LevelTree.lev (LevelTree.ancestor
          ((finiteNumericH K k N).kptOriginal family hAvoidH c)
          (hPosition k i.val k) (hWithin i.val i.property)) =
          hPosition k i.val k :=
      LevelTree.level_ancestor _ _ _
    rw [hLev]
    exact numericHTopLevel_ne_lowerGeneration k i.val p r hrk

/-- At most q+1 seed nodes are introduced from q top-generation
positions (duplicates may reduce their number). -/
theorem numericHTopGenerationSeeds_card_le
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd) (k N : Nat)
    (hAvoidH : ∀ bad, bad ∈ family →
      bad.Avoids (finiteNumericHL K k N))
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val) :
    (numericHTopGenerationSeeds
      family K k N hAvoidH c blocks hWithin).card ≤ blocks.card + 1 := by
  classical
  unfold numericHTopGenerationSeeds
  let root : AdmissibleKptNode family :=
    (finiteNumericH K k N).kptOriginal family hAvoidH c
  let S : Finset (AdmissibleKptNode family) :=
    blocks.attach.image (fun i : Subtype (fun i : Nat => i ∈ blocks) =>
      LevelTree.ancestor root (hPosition k i.val k) (hWithin i.val i.property))
  change (insert root S).card ≤ blocks.card + 1
  have hImage : S.card ≤ blocks.card := by
    calc
      S.card ≤ blocks.attach.card := Finset.card_image_le
      _ = blocks.card := by simp
  by_cases hRoot : root ∈ S
  · simp [Finset.card_insert_of_mem hRoot]
    omega
  · simp [Finset.card_insert_of_not_mem hRoot]
    omega

/-- The promised I1 conclusion for the ACTUAL finite top-generation
seed family, with no remaining hand-supplied no-intermediate-seeds
premise: every selected real intermediate closure node has the
precise higher-original numeric H meet charge. -/
theorem numericHTopSeeds_realI1_meet_charge
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (K : AgeTestModel db du dd)
    (hCarrier : ∀ i : Nat, i ∈ K.carrier)
    (hAvoidK : ∀ bad, bad ∈ family → bad.Avoids K)
    (k N : Nat) (hk : 0 < k)
    (c : Fin N) (blocks : Finset Nat)
    (hWithin : ∀ i : Nat, i ∈ blocks →
      hPosition k i k ≤ (finiteNumericH K k N).freeLevel c.val)
    (I : Set Nat)
    (z : AdmissibleKptNode family)
    (hz : z ∈ SMTree.Envelope.closure
      (admissibleKptSTree family) I
      (numericHTopGenerationSeeds family K k N
        (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
        c blocks hWithin))
    (p r : Nat) (hr : 0 < r) (hrk : r < k)
    (hLevel : LevelTree.lev z = hPosition k p r) :
    ∃ v w : Fin N,
      v ∈ ambientStagePool (finiteNumericH K k N)
        ({c} : Set (Fin N)) I ∧
      w ∈ ambientStagePool (finiteNumericH K k N)
        ({c} : Set (Fin N)) I ∧
      NumericHMeetCharge K.binary k v.val w.val p r := by
  exact numericH_real_I1_node_has_higher_original_charge
    family K hCarrier hAvoidK k N hk I
    (numericHTopGenerationSeeds family K k N
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin)
    ({c} : Set (Fin N))
    (numericHTopGenerationSeeds_subset_rootPool
      family K k N
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin)
    z hz p r hr (Nat.le_of_lt hrk) hLevel
    (numericHTopGenerationSeeds_noIntermediateReal
      family K k N
      (finiteNumericH_avoids_family family K hCarrier k N hAvoidK)
      c blocks hWithin p r hr hrk)

end SuccessorTree.V10
