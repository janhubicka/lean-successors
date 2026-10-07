import SuccessorTree.EnvelopePullback
import Mathlib.Tactic

/-!
# Pulling envelope closure through a noninteresting level

Local lemmas used to instantiate the one-level pullback theorem at a stage of
the manuscript's envelope algorithm.
-/

namespace SuccessorTree
namespace SMTree
namespace Envelope

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Literal pointwise fixing through a source level. -/
def FixesThrough (F : ShapeMap S) (n : Nat) : Prop :=
  ∀ ⦃x : T⦄, LevelTree.lev x ≤ n → F x = x

/-- Pointwise fixing of a finite parameter list fixes its image list. -/
private theorem list_map_eq_self_of_pointwise
    (F : T → T) (p : List T)
    (h : ∀ x ∈ p, F x = x) :
    p.map F = p := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : F x = x := h x (by simp)
      have hxs : ∀ y ∈ xs, F y = y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih hxs]

/-- If a shape map fixes through level `n`, then the next source prefix still
lies below the image. This is the formal version of the sentence used in the
base case of the envelope invariant. -/
theorem nextPrefix_le_map_of_fixesThrough
    (F : ShapeMap S) (n : Nat) (hfix : FixesThrough F n)
    {z : T} (hnz : n < LevelTree.lev z) :
    LevelTree.ancestor z (n + 1) (Nat.succ_le_iff.mpr hnz) ≤ F z := by
  let a := LevelTree.ancestor z n (Nat.le_of_lt hnz)
  let b := LevelTree.ancestor z (n + 1) (Nat.succ_le_iff.mpr hnz)
  have haz : a ≤ z := LevelTree.ancestor_le z n (Nat.le_of_lt hnz)
  have hbz : b ≤ z :=
    LevelTree.ancestor_le z (n + 1) (Nat.succ_le_iff.mpr hnz)
  have halev : LevelTree.lev a = n :=
    LevelTree.level_ancestor z n (Nat.le_of_lt hnz)
  have hblev : LevelTree.lev b = n + 1 :=
    LevelTree.level_ancestor z (n + 1) (Nat.succ_le_iff.mpr hnz)
  have hab : a ≤ b := by
    rcases LevelTree.comparable_below haz hbz with h | h
    · exact h
    · have hlev := LevelTree.level_le_of_le h
      omega
  have hcov : a ⋖ b := by
    apply LevelTree.covBy_of_le_level_succ hab
    omega
  obtain ⟨p, c, hs⟩ := S.s3 hcov
  have hFa : F a = a := hfix (by simpa [halev])
  have hpfix : ∀ x ∈ p, F x = x := by
    intro x hx
    apply hfix
    have hxlt := S.parameter_level_lt hs hx
    rw [halev] at hxlt
    omega
  have hpmap : p.map F = p :=
    list_map_eq_self_of_pointwise F p hpfix
  obtain ⟨d, hFd, hdb⟩ := F.weak_succ' hs
  have hFd' : S.succ a p c = some d := by
    simpa [hFa, hpmap] using hFd
  have hdbEq : d = b :=
    Option.some.inj (hFd'.symm.trans hs)
  subst d
  exact hdb.trans (F.map_le_of_le hbz)

/-- A fixed prefix is the corresponding prefix of the image. -/
theorem prefix_of_map_eq_of_fixesThrough
    (F : ShapeMap S) (n : Nat) (hfix : FixesThrough F n)
    {z : T} (hnz : n ≤ LevelTree.lev z) :
    let a := LevelTree.ancestor z n hnz
    a ≤ F z := by
  intro a
  have haz : a ≤ z := LevelTree.ancestor_le z n hnz
  have halev : LevelTree.lev a = n := LevelTree.level_ancestor z n hnz
  have hFa : F a = a := hfix (by simpa [halev])
  have hle : F a ≤ F z := F.map_le_of_le haz
  simpa [hFa] using hle

/-- If `D` extends the target crossing map on `C`, then after pulling `C` back
through a map fixing through `m`, `D` extends the source crossing map as well. -/
theorem pullback_crossing_of_extension
    (G D : ShapeMap S) (m : Nat) (hfix : FixesThrough G m)
    (C : Set T)
    (hD : ∀ ⦃c : T⦄, c ∈ C → ∀ (hmc : m < LevelTree.lev c),
      D (LevelTree.ancestor c m (Nat.le_of_lt hmc)) =
        LevelTree.ancestor c (m + 1) (Nat.succ_le_iff.mpr hmc)) :
    ∀ ⦃z : T⦄, z ∈ G ⁻¹' C → ∀ (hmz : m < LevelTree.lev z),
      D (LevelTree.ancestor z m (Nat.le_of_lt hmz)) =
        LevelTree.ancestor z (m + 1) (Nat.succ_le_iff.mpr hmz) := by
  intro z hz hmz
  let a := LevelTree.ancestor z m (Nat.le_of_lt hmz)
  let b := LevelTree.ancestor z (m + 1) (Nat.succ_le_iff.mpr hmz)
  have halev : LevelTree.lev a = m :=
    LevelTree.level_ancestor z m (Nat.le_of_lt hmz)
  have hblev : LevelTree.lev b = m + 1 :=
    LevelTree.level_ancestor z (m + 1) (Nat.succ_le_iff.mpr hmz)
  have haGz : a ≤ G z := prefix_of_map_eq_of_fixesThrough G m hfix (Nat.le_of_lt hmz)
  have hbGz : b ≤ G z := nextPrefix_le_map_of_fixesThrough G m hfix hmz
  have hmGz : m < LevelTree.lev (G z) := by
    have h := LevelTree.level_le_of_le hbGz
    rw [hblev] at h
    omega
  have haEq :
      a = LevelTree.ancestor (G z) m (Nat.le_of_lt hmGz) :=
    LevelTree.eq_ancestor_of_le haGz halev (Nat.le_of_lt hmGz)
  have hm1Gz : m + 1 ≤ LevelTree.lev (G z) := Nat.succ_le_iff.mpr hmGz
  have hbEq :
      b = LevelTree.ancestor (G z) (m + 1) hm1Gz :=
    LevelTree.eq_ancestor_of_le hbGz hblev hm1Gz
  change D a = b
  rw [haEq, hbEq]
  exact hD hz hmGz

/-- Parameter closure pulls back through a shape map at source levels whose
image levels are known to belong to the target closure index set. -/
theorem preimage_parameterClosed_above
    (H : SMTree S) (G : ShapeMap S) (m : Nat)
    (C : Set T) (I : Set Nat)
    (hC : ParameterClosedOver S C I)
    (hI : ∀ ⦃z : T⦄, G z ∈ C → ∀ ⦃j : Nat⦄,
      m < j → j < LevelTree.lev z → H.levelMap G j ∈ I) :
    ParameterClosedOver S (G ⁻¹' C) {j | m < j} := by
  intro z hz j hj hjz p c hs y hy
  let a := LevelTree.ancestor z j (Nat.le_of_lt hjz)
  let b := LevelTree.ancestor z (j + 1) (Nat.succ_le_iff.mpr hjz)
  have haz : a ≤ z := LevelTree.ancestor_le z j (Nat.le_of_lt hjz)
  have hbz : b ≤ z :=
    LevelTree.ancestor_le z (j + 1) (Nat.succ_le_iff.mpr hjz)
  have halev : LevelTree.lev a = j :=
    LevelTree.level_ancestor z j (Nat.le_of_lt hjz)
  obtain ⟨d, hGd, hdb⟩ := G.weak_succ' hs
  have hGaZ : G a ≤ G z := G.map_le_of_le haz
  have hGbZ : G b ≤ G z := G.map_le_of_le hbz
  have hdZ : d ≤ G z := hdb.trans hGbZ
  let q := H.levelMap G j
  have hGalev : LevelTree.lev (G a) = q := by
    calc
      LevelTree.lev (G a) = H.levelMap G (LevelTree.lev a) :=
        (H.levelMap_eq G (a := a)).symm
      _ = q := by simp [q, halev]
  have hqz : q < LevelTree.lev (G z) := by
    have hmono := H.levelMap_strictMono G hjz
    have hzlev := H.levelMap_eq G (a := z)
    dsimp [q]
    exact hmono.trans_eq hzlev
  have hGaAnc :
      G a = LevelTree.ancestor (G z) q (Nat.le_of_lt hqz) :=
    LevelTree.eq_ancestor_of_le hGaZ hGalev (Nat.le_of_lt hqz)
  have hdlev : LevelTree.lev d = q + 1 := by
    have hcov := S.covBy_of_succ_eq_some hGd
    rw [LevelTree.covBy_level_eq hcov, hGalev]
  have hq1z : q + 1 ≤ LevelTree.lev (G z) := Nat.succ_le_iff.mpr hqz
  have hdAnc : d = LevelTree.ancestor (G z) (q + 1) hq1z :=
    LevelTree.eq_ancestor_of_le hdZ hdlev hq1z
  have htarget := hGd
  rw [hGaAnc, hdAnc] at htarget
  have hqI : q ∈ I := hI hz hj hjz
  have hGy : G y ∈ p.map G := List.mem_map.mpr ⟨y, hy, rfl⟩
  exact hC hz hqI hqz htarget hGy

/-- If the target closure contains no node on `m` and `G` fixes through `m`,
then neither does its preimage. -/
theorem preimage_has_no_level_of_fixesThrough
    (G : ShapeMap S) (m : Nat) (hfix : FixesThrough G m)
    {C : Set T} (hno : ∀ ⦃x : T⦄, x ∈ C → LevelTree.lev x ≠ m) :
    ∀ ⦃z : T⦄, z ∈ G ⁻¹' C → LevelTree.lev z ≠ m := by
  intro z hz hzlev
  have hGz : G z = z := hfix (by omega)
  apply hno hz
  simpa [hGz] using hzlev


/-- A shape map cannot send source level `n` below `n`. -/
theorem sourceLevel_le_levelMap
    (H : SMTree S) (G : ShapeMap S) (n : Nat) :
    n ≤ H.levelMap G n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hs : H.levelMap G n < H.levelMap G (n + 1) :=
        H.levelMap_strictMono G (by omega)
      omega

/-- If a target set is bounded by `ell`, then every source level above `m`
which occurs before one of its pulled-back nodes maps to an indexed target
level, provided all range levels in that interval are indexed. -/
theorem pulledBack_sourceLevel_indexed
    (H : SMTree S) (G : ShapeMap S) (m ell : Nat)
    (C : Set T) (I : Set Nat)
    (hbound : C ⊆ levelLe ell)
    (hindexed : ∀ ⦃q : Nat⦄, q ∈ G.levelRange → m < q → q ≤ ell → q ∈ I) :
    ∀ ⦃z : T⦄, G z ∈ C → ∀ ⦃j : Nat⦄,
      m < j → j < LevelTree.lev z → H.levelMap G j ∈ I := by
  intro z hz j hmj hjz
  have hqRange : H.levelMap G j ∈ G.levelRange := by
    rw [← H.range_levelMap G]
    exact ⟨j, rfl⟩
  have hmq : m < H.levelMap G j := by
    have hm0 := sourceLevel_le_levelMap H G m
    have hm1 := H.levelMap_strictMono G hmj
    omega
  have hqz : H.levelMap G j < LevelTree.lev (G z) := by
    have hmono := H.levelMap_strictMono G hjz
    exact hmono.trans_eq (H.levelMap_eq G (a := z))
  have hzBound : LevelTree.lev (G z) ≤ ell := hbound hz
  exact hindexed hqRange hmq (by omega)

/-- Parameter closure therefore pulls back from a bounded target closure when
its met range levels are precisely among the indexed levels of the invariant. -/
theorem preimage_parameterClosed_of_bounded_indexed
    (H : SMTree S) (G : ShapeMap S) (m ell : Nat)
    (C : Set T) (I : Set Nat)
    (hC : ParameterClosedOver S C I)
    (hbound : C ⊆ levelLe ell)
    (hindexed : ∀ ⦃q : Nat⦄, q ∈ G.levelRange → m < q → q ≤ ell → q ∈ I) :
    ParameterClosedOver S (G ⁻¹' C) {j | m < j} :=
  preimage_parameterClosed_above H G m C I hC
    (pulledBack_sourceLevel_indexed H G m ell C I hbound hindexed)

/-- The complete noninteresting-stage pullback: if the later map fixes through
`m`, the target closure has no node at `m`, the target parameters used above
`m` lie on indexed levels, and the one-level factor extends the crossing map,
then every pulled-back closure node lies in the factor's range. -/
theorem preimage_subset_range_of_oneLevel
    (H : SMTree S) (G D : ShapeMap S) (m : Nat)
    (hfix : FixesThrough G m)
    (hskip : D.SkipsOnly m) (hE : PullbackDefined S D)
    (C : Set T) (I : Set Nat)
    (hC : ParameterClosedOver S C I)
    (hI : ∀ ⦃z : T⦄, G z ∈ C → ∀ ⦃j : Nat⦄,
      m < j → j < LevelTree.lev z → H.levelMap G j ∈ I)
    (hno : ∀ ⦃x : T⦄, x ∈ C → LevelTree.lev x ≠ m)
    (hD : ∀ ⦃c : T⦄, c ∈ C → ∀ (hmc : m < LevelTree.lev c),
      D (LevelTree.ancestor c m (Nat.le_of_lt hmc)) =
        LevelTree.ancestor c (m + 1) (Nat.succ_le_iff.mpr hmc)) :
    G ⁻¹' C ⊆ Set.range D := by
  apply subset_range_of_oneLevel H D m hskip hE (G ⁻¹' C)
  · exact preimage_parameterClosed_above H G m C I hC hI
  · exact preimage_has_no_level_of_fixesThrough G m hfix hno
  · exact pullback_crossing_of_extension G D m hfix C hD


/-- Manuscript-ready form of the noninteresting-stage argument. The boundedness
of the closure and the outer invariant supply the parameter-index hypothesis. -/
theorem preimage_subset_range_of_bounded_indexed
    (H : SMTree S) (G D : ShapeMap S) (m ell : Nat)
    (hfix : FixesThrough G m)
    (hskip : D.SkipsOnly m) (hE : PullbackDefined S D)
    (C : Set T) (I : Set Nat)
    (hC : ParameterClosedOver S C I)
    (hbound : C ⊆ levelLe ell)
    (hindexed : ∀ ⦃q : Nat⦄, q ∈ G.levelRange → m < q → q ≤ ell → q ∈ I)
    (hno : ∀ ⦃x : T⦄, x ∈ C → LevelTree.lev x ≠ m)
    (hD : ∀ ⦃c : T⦄, c ∈ C → ∀ (hmc : m < LevelTree.lev c),
      D (LevelTree.ancestor c m (Nat.le_of_lt hmc)) =
        LevelTree.ancestor c (m + 1) (Nat.succ_le_iff.mpr hmc)) :
    G ⁻¹' C ⊆ Set.range D := by
  exact preimage_subset_range_of_oneLevel H G D m hfix hskip hE C I hC
    (pulledBack_sourceLevel_indexed H G m ell C I hbound hindexed)
    hno hD

end Envelope
end SMTree
end SuccessorTree
