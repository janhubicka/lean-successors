import SuccessorTree.Successor
import Mathlib.Tactic

/-!
# Shape-preserving maps

Formalization of Definition `def:shape-pres` and the basic pre-pigeonhole
properties used in the successor-tree paper.
-/

namespace SuccessorTree

structure ShapeMap {T : Type u} {Label : Type v}
    [PartialOrder T] [LevelTree T] (S : STree T Label) where
  toFun : T → T
  injective' : Function.Injective toFun
  level_preserving' : ∀ {a b : T}, LevelTree.lev a = LevelTree.lev b →
    LevelTree.lev (toFun a) = LevelTree.lev (toFun b)
  weak_succ' : ∀ {a b : T} {p : List T} {c : Label},
    S.succ a p c = some b →
      ∃ d : T,
        S.succ (toFun a) (p.map toFun) c = some d ∧ d ≤ toFun b
  root_le' : ∀ {a : T}, LevelTree.lev a = 0 → a ≤ toFun a

namespace ShapeMap

variable {T : Type u} {Label : Type v} [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

instance : CoeFun (ShapeMap S) (fun _ => T → T) := ⟨ShapeMap.toFun⟩

theorem injective (F : ShapeMap S) : Function.Injective F := F.injective'

theorem level_eq_of_level_eq (F : ShapeMap S) {a b : T}
    (h : LevelTree.lev a = LevelTree.lev b) :
    LevelTree.lev (F a) = LevelTree.lev (F b) :=
  F.level_preserving' h

/-- Weak successor preservation already implies strict order preservation on
one tree edge. -/
theorem map_lt_of_covBy (F : ShapeMap S) {a b : T} (hab : a ⋖ b) :
    F a < F b := by
  obtain ⟨p, c, hsucc⟩ := S.s3 hab
  obtain ⟨d, hFd, hdb⟩ := F.weak_succ' hsucc
  have hcover : F a ⋖ d := S.covBy_of_succ_eq_some hFd
  exact lt_of_lt_of_le hcover.lt hdb

/-- Shape-preserving maps preserve strict tree order. -/
theorem map_lt_of_lt (F : ShapeMap S) {a b : T} (hab : a < b) :
    F a < F b := by
  induction hdiff : LevelTree.lev b - LevelTree.lev a using Nat.strong_induction_on generalizing a b with
  | h d ih =>
      obtain ⟨c, hac, hcb⟩ := LevelTree.exists_covBy_between hab
      by_cases hbc : c = b
      · subst b
        exact F.map_lt_of_covBy hac
      · have hcb' : c < b := lt_of_le_of_ne hcb hbc
        have hfirst : F a < F c := F.map_lt_of_covBy hac
        have hlevels : LevelTree.lev c = LevelTree.lev a + 1 :=
          LevelTree.covBy_level_eq hac
        have habLevels : LevelTree.lev a < LevelTree.lev b :=
          LevelTree.lt_level_lt hab
        have hsmaller : LevelTree.lev b - LevelTree.lev c < d := by
          rw [← hdiff]
          omega
        have htail : F c < F b :=
          ih (LevelTree.lev b - LevelTree.lev c) hsmaller hcb' rfl
        exact hfirst.trans htail

theorem map_le_of_le (F : ShapeMap S) {a b : T} (hab : a ≤ b) :
    F a ≤ F b := by
  rcases hab.eq_or_lt with h | h
  · simpa [h]
  · exact (F.map_lt_of_lt h).le

/-- Paper Proposition `prop:shape-pres`, clause (ii), in a formulation
which does not introduce separate partial notation for \(\Dp\) and \(\Dc\):
the decomposition of the next predecessor level remains defined after applying
a shape-preserving map, and its image lies below the image of the whole node. -/
theorem preserves_decomposition (F : ShapeMap S) (a : T) (n : Nat)
    (hn : n < LevelTree.lev a) :
    ∃ p : List T, ∃ c : Label, ∃ d : T,
      let hn0 : n ≤ LevelTree.lev a := Nat.le_of_lt hn
      let hn1 : n + 1 ≤ LevelTree.lev a := Nat.succ_le_iff.mpr hn
      let x := LevelTree.ancestor a n hn0
      let y := LevelTree.ancestor a (n + 1) hn1
      S.succ x p c = some y ∧
      S.succ (F x) (p.map F) c = some d ∧
      d ≤ F a := by
  let hn0 : n ≤ LevelTree.lev a := Nat.le_of_lt hn
  let hn1 : n + 1 ≤ LevelTree.lev a := Nat.succ_le_iff.mpr hn
  let x := LevelTree.ancestor a n hn0
  let y := LevelTree.ancestor a (n + 1) hn1
  have hxa : x ≤ a := LevelTree.ancestor_le a n hn0
  have hya : y ≤ a := LevelTree.ancestor_le a (n + 1) hn1
  have hxlev : LevelTree.lev x = n := LevelTree.level_ancestor a n hn0
  have hylev : LevelTree.lev y = n + 1 :=
    LevelTree.level_ancestor a (n + 1) hn1
  have hxy : x ≤ y := by
    rcases LevelTree.comparable_below hxa hya with h | h
    · exact h
    · have hlev := LevelTree.level_le_of_le h
      omega
  have hcover : x ⋖ y := by
    apply LevelTree.covBy_of_le_level_succ hxy
    omega
  obtain ⟨p, c, hsucc⟩ := S.s3 hcover
  obtain ⟨d, hFd, hdy⟩ := F.weak_succ' hsucc
  refine ⟨p, c, d, ?_⟩
  dsimp [hn0, hn1, x, y]
  refine ⟨hsucc, hFd, ?_⟩
  exact hdy.trans (F.map_le_of_le hya)

/-- Relative order of levels is preserved, even for incomparable nodes. -/
theorem level_lt_of_level_lt (F : ShapeMap S) {a b : T}
    (hab : LevelTree.lev a < LevelTree.lev b) :
    LevelTree.lev (F a) < LevelTree.lev (F b) := by
  have hle : LevelTree.lev a ≤ LevelTree.lev b := Nat.le_of_lt hab
  let c := LevelTree.ancestor b (LevelTree.lev a) hle
  have hcb : c ≤ b := LevelTree.ancestor_le b (LevelTree.lev a) hle
  have hcLevel : LevelTree.lev c = LevelTree.lev a := by
    simp [c, LevelTree.level_ancestor]
  have hcbne : c ≠ b := by
    intro h
    have hlevels := congrArg LevelTree.lev h
    omega
  have hcb' : c < b := lt_of_le_of_ne hcb hcbne
  have hmap := F.map_lt_of_lt hcb'
  have hFaFc : LevelTree.lev (F a) = LevelTree.lev (F c) :=
    F.level_eq_of_level_eq hcLevel.symm
  have hlev := LevelTree.lt_level_lt hmap
  omega

/-- The identity map is shape-preserving. -/
def id (S : STree T Label) : ShapeMap S where
  toFun := fun a => a
  injective' := Function.injective_id
  level_preserving' := by intro a b h; exact h
  weak_succ' := by
    intro a b p c h
    refine ⟨b, ?_, le_rfl⟩
    simpa using h
  root_le' := by intro a ha; exact le_rfl

@[simp] theorem id_apply (a : T) : (id S) a = a := rfl

/-- Composition of shape-preserving maps. The proof uses order preservation
for the outer map; this is the dependency hidden by the paper's phrase
“follows directly from the definition”. -/
def comp (F G : ShapeMap S) : ShapeMap S where
  toFun := fun a => F (G a)
  injective' := F.injective.comp G.injective
  level_preserving' := by
    intro a b hab
    exact F.level_eq_of_level_eq (G.level_eq_of_level_eq hab)
  weak_succ' := by
    intro a b p c hab
    obtain ⟨d, hGd, hdb⟩ := G.weak_succ' hab
    obtain ⟨e, hFe, hed⟩ := F.weak_succ' hGd
    refine ⟨e, ?_, hed.trans (F.map_le_of_le hdb)⟩
    simpa [List.map_map, Function.comp_def] using hFe
  root_le' := by
    intro a ha
    have haG : a ≤ G a := G.root_le' ha
    have haF : a ≤ F a := F.root_le' ha
    exact haF.trans (F.map_le_of_le haG)

@[simp] theorem comp_apply (F G : ShapeMap S) (a : T) :
    (F.comp G) a = F (G a) := rfl

/-- Successive members of a fusion sequence agree on every node whose level
has already been frozen. -/
def FusionStable (F : Nat → ShapeMap S) : Prop :=
  ∀ (i : Nat) (a : T), LevelTree.lev a ≤ i → F i a = F (i + 1) a

theorem fusion_stable_add (F : Nat → ShapeMap S) (hF : FusionStable F)
    (a : T) (d : Nat) :
    F (LevelTree.lev a + d) a = F (LevelTree.lev a) a := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hs := hF (LevelTree.lev a + d) a (by omega)
      calc
        F (LevelTree.lev a + (d + 1)) a =
            F ((LevelTree.lev a + d) + 1) a := by congr 1 <;> omega
        _ = F (LevelTree.lev a + d) a := hs.symm
        _ = F (LevelTree.lev a) a := ih

theorem fusion_stable_of_le (F : Nat → ShapeMap S) (hF : FusionStable F)
    (a : T) {i : Nat} (hi : LevelTree.lev a ≤ i) :
    F i a = F (LevelTree.lev a) a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact fusion_stable_add F hF a d

private theorem list_map_eq_of_mem_eq
    (p : List T) (f g : T → T)
    (h : ∀ x ∈ p, f x = g x) :
    p.map f = p.map g := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.map_cons]
      rw [hx, ih hxs]

/-- The pointwise fusion limit from Proposition `prop:shape-pres`. -/
noncomputable def fusionLimit (F : Nat → ShapeMap S) (hF : FusionStable F) :
    ShapeMap S where
  toFun := fun a => F (LevelTree.lev a) a
  injective' := by
    intro a b hab
    let i := max (LevelTree.lev a) (LevelTree.lev b)
    have hai : LevelTree.lev a ≤ i := Nat.le_max_left _ _
    have hbi : LevelTree.lev b ≤ i := Nat.le_max_right _ _
    have haeq : F i a = F (LevelTree.lev a) a :=
      fusion_stable_of_le F hF a hai
    have hbeq : F i b = F (LevelTree.lev b) b :=
      fusion_stable_of_le F hF b hbi
    apply (F i).injective
    calc
      F i a = F (LevelTree.lev a) a := haeq
      _ = F (LevelTree.lev b) b := hab
      _ = F i b := hbeq.symm
  level_preserving' := by
    intro a b hab
    rw [← hab]
    exact (F (LevelTree.lev a)).level_eq_of_level_eq hab
  weak_succ' := by
    intro a b p c hsucc
    let k := LevelTree.lev a
    have hbLevel : LevelTree.lev b = k + 1 := by
      exact LevelTree.covBy_level_eq (S.covBy_of_succ_eq_some hsucc)
    have haStable : F (k + 1) a = F k a :=
      (hF k a (by simp [k])).symm
    have hbDef : F (LevelTree.lev b) b = F (k + 1) b := by
      rw [hbLevel]
    have hparam : ∀ x ∈ p,
        F (LevelTree.lev x) x = F (k + 1) x := by
      intro x hx
      have hxlt : LevelTree.lev x < k :=
        S.parameter_level_lt hsucc hx
      have hxle : LevelTree.lev x ≤ k + 1 := by omega
      exact (fusion_stable_of_le F hF x hxle).symm
    have hmap :
        p.map (fun x => F (LevelTree.lev x) x) =
          p.map (fun x => F (k + 1) x) :=
      list_map_eq_of_mem_eq p
        (fun x => F (LevelTree.lev x) x)
        (fun x => F (k + 1) x) hparam
    obtain ⟨d, hd, hdb⟩ := (F (k + 1)).weak_succ' hsucc
    refine ⟨d, ?_, ?_⟩
    · simpa [k, haStable, hmap] using hd
    · simpa [hbDef] using hdb
  root_le' := by
    intro a ha
    simpa [ha] using (F 0).root_le' ha

@[simp] theorem fusionLimit_apply (F : Nat → ShapeMap S)
    (hF : FusionStable F) (a : T) :
    fusionLimit F hF a = F (LevelTree.lev a) a := rfl

/-- The fusion limit agrees with the prescribed stage on every frozen level. -/
theorem fusionLimit_eq_stage (F : Nat → ShapeMap S) (hF : FusionStable F)
    {i : Nat} {a : T} (ha : LevelTree.lev a ≤ i) :
    fusionLimit F hF a = F i a := by
  exact (fusion_stable_of_le F hF a ha).symm

/-- The pointwise fusion limit is unique with the stabilization property. -/
theorem fusionLimit_unique (F : Nat → ShapeMap S) (hF : FusionStable F)
    (G : ShapeMap S)
    (hG : ∀ (i : Nat) (a : T), LevelTree.lev a ≤ i → G a = F i a) :
    G.toFun = (fusionLimit F hF).toFun := by
  funext a
  exact hG (LevelTree.lev a) a le_rfl

end ShapeMap

end SuccessorTree
