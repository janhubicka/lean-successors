import SuccessorTree.FreeAncestralLevelTree
import SuccessorTree.Successor
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! # Successor helpers for the free ancestral tree

The intrinsic code stores only an ordered tuple of ancestor levels. This file
decodes that tuple to the actual predecessor nodes expected by the successor
API and defines the corresponding immediate child.
-/

namespace SuccessorTree
namespace FreeAncestral

universe u

variable {Label : Type u} {arity : Nat} [Fintype Label]

/-- Decode an intrinsic ancestral parameter tuple at the base node a to the
ordered list of actual predecessor nodes used by the external successor API. -/
noncomputable def paramNodes
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    List (Node Label arity) :=
  List.ofFn fun j =>
    LevelTree.ancestor a (t.value j).val
      (Nat.le_of_lt (t.value j).isLt)

@[simp] theorem length_paramNodes
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    (paramNodes a t).length = t.len.val := by
  simp [paramNodes]

theorem mem_paramNodes_level_lt
    {a x : Node Label arity}
    {t : ParamTuple arity a.level}
    (hx : x ∈ paramNodes a t) :
    LevelTree.lev x < LevelTree.lev a := by
  simp only [paramNodes, List.mem_ofFn] at hx
  obtain ⟨j, rfl⟩ := hx
  rw [LevelTree.level_ancestor]
  exact (t.value j).isLt

/-- The immediate history child coded by one intrinsic transition. -/
def child :
    (a : Node Label arity) →
    ParamTuple arity a.level →
    Label →
    Node Label arity
  | ⟨n, h⟩, t, c =>
      ⟨n + 1, History.step h ⟨c, t⟩⟩

@[simp] theorem child_level
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    (child a t c).level = a.level + 1 := by
  rcases a with ⟨n, h⟩
  rfl

theorem base_le_child
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    a ≤ child a t c := by
  rcases a with ⟨n, h⟩
  exact Prefix.step (Prefix.refl h) ⟨c, t⟩

theorem base_covBy_child
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    a ⋖ child a t c := by
  apply LevelTree.covBy_of_le_level_succ
    (base_le_child a t c)
  change (child a t c).level = a.level + 1
  exact child_level a t c

/-- A parameter list is intrinsic at a when it is the canonical decoding of
one bounded ancestral tuple. -/
def HasParams
    (a : Node Label arity)
    (p : List (Node Label arity)) : Prop :=
  ∃ t : ParamTuple arity a.level, paramNodes a t = p

noncomputable def chosenTuple
    (a : Node Label arity)
    (p : List (Node Label arity))
    (h : HasParams a p) :
    ParamTuple arity a.level :=
  Classical.choose h

theorem chosenTuple_spec
    (a : Node Label arity)
    (p : List (Node Label arity))
    (h : HasParams a p) :
    paramNodes a (chosenTuple a p h) = p :=
  Classical.choose_spec h

/-- Canonical free successor. It is defined exactly on canonical ancestral
parameter lists. -/
noncomputable def freeSucc
    (a : Node Label arity)
    (p : List (Node Label arity))
    (c : Label) :
    Option (Node Label arity) := by
  classical
  exact if h : HasParams a p then
    some (child a (chosenTuple a p h) c)
  else
    none

theorem freeSucc_eq_some_data
    {a b : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (h : freeSucc a p c = some b) :
    ∃ t : ParamTuple arity a.level,
      paramNodes a t = p ∧ b = child a t c := by
  classical
  unfold freeSucc at h
  split at h
  next hp =>
    refine ⟨chosenTuple a p hp, chosenTuple_spec a p hp, ?_⟩
    exact (Option.some.inj h).symm
  next hp =>
    simp at h

/-- Parameter levels, forgetting the actual ancestor nodes. -/
def levelList {n : Nat} (t : ParamTuple arity n) : List Nat :=
  List.ofFn fun j => (t.value j).val

theorem map_level_paramNodes
    (a : Node Label arity)
    (t : ParamTuple arity a.level) :
    (paramNodes a t).map Node.level = levelList t := by
  simp only [paramNodes, levelList, List.map_ofFn]
  have hfun :
      (Node.level ∘ fun j =>
        LevelTree.ancestor a (t.value j).val
          (Nat.le_of_lt (t.value j).isLt)) =
        (fun j => (t.value j).val) := by
    funext j
    simpa only [Node.level] using
      (LevelTree.level_ancestor
        a (t.value j).val (Nat.le_of_lt (t.value j).isLt))
  exact congrArg List.ofFn hfun

theorem levelList_injective :
    Function.Injective (levelList : ParamTuple arity n → List Nat) := by
  intro t u h
  rcases t with ⟨lt, vt⟩
  rcases u with ⟨lu, vu⟩
  simp only [levelList] at h
  have hlen : lt.val = lu.val := by
    simpa using congrArg List.length h
  have hlt : lt = lu := Fin.ext hlen
  subst lu
  have hfun :
      (fun j : Fin lt.val => (vt j).val) =
        (fun j : Fin lt.val => (vu j).val) :=
    List.ofFn_injective h
  have hv : vt = vu := by
    funext j
    apply Fin.ext
    exact congrFun hfun j
  subst vu
  rfl

theorem paramNodes_injective (a : Node Label arity) :
    Function.Injective (paramNodes a) := by
  intro t u h
  apply levelList_injective
  have hm := congrArg (List.map Node.level) h
  simpa [map_level_paramNodes] using hm

/-- Read the last intrinsic label from a total history node. -/
def lastLabelNode : Node Label arity → Option Label
  | ⟨0, _⟩ => none
  | ⟨n + 1, h⟩ => some (lastCode h).label

/-- Read the last ancestral parameter-level tuple as a plain list. -/
def lastParamLevelsNode : Node Label arity → List Nat
  | ⟨0, _⟩ => []
  | ⟨n + 1, h⟩ => levelList (lastCode h).params

@[simp] theorem lastLabelNode_child
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    lastLabelNode (child a t c) = some c := by
  rcases a with ⟨n, h⟩
  rfl

@[simp] theorem lastParamLevelsNode_child
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    lastParamLevelsNode (child a t c) = levelList t := by
  rcases a with ⟨n, h⟩
  rfl

theorem base_eq_of_child_eq
    {a b : Node Label arity}
    {t : ParamTuple arity a.level}
    {u : ParamTuple arity b.level}
    {c d : Label}
    (h : child a t c = child b u d) :
    a = b := by
  have ha : a ⋖ child a t c := base_covBy_child a t c
  have hb : b ⋖ child a t c := by
    simpa [h] using base_covBy_child b u d
  have hlev : LevelTree.lev a = LevelTree.lev b := by
    have hla := LevelTree.covBy_level_eq ha
    have hlb := LevelTree.covBy_level_eq hb
    omega
  rcases LevelTree.comparable_below ha.le hb.le with hab | hba
  · exact LevelTree.same_level_of_le hab hlev
  · exact (LevelTree.same_level_of_le hba hlev.symm).symm

theorem child_eq_data
    {a : Node Label arity}
    {t u : ParamTuple arity a.level}
    {c d : Label}
    (h : child a t c = child a u d) :
    t = u ∧ c = d := by
  have hcSome :
      (some c : Option Label) = some d := by
    simpa using congrArg lastLabelNode h
  have hc : c = d := Option.some.inj hcSome
  have htLevels : levelList t = levelList u := by
    simpa using congrArg lastParamLevelsNode h
  exact ⟨levelList_injective htLevels, hc⟩

theorem freeSucc_s2
    {a b x : Node Label arity}
    {p q : List (Node Label arity)}
    {c d : Label}
    (ha : freeSucc a p c = some x)
    (hb : freeSucc b q d = some x) :
    a = b ∧ p = q ∧ c = d := by
  obtain ⟨t, htp, htx⟩ := freeSucc_eq_some_data ha
  obtain ⟨u, huq, hux⟩ := freeSucc_eq_some_data hb
  have hchild : child a t c = child b u d := htx.symm.trans hux
  have hab : a = b := base_eq_of_child_eq hchild
  subst b
  have hdata : t = u ∧ c = d := child_eq_data hchild
  rcases hdata with ⟨htu, hcd⟩
  subst u
  exact ⟨rfl, htp.symm.trans huq, hcd⟩

theorem freeSucc_paramNodes
    (a : Node Label arity)
    (t : ParamTuple arity a.level)
    (c : Label) :
    freeSucc a (paramNodes a t) c = some (child a t c) := by
  classical
  unfold freeSucc
  split
  next hp =>
    have hchosen :
        chosenTuple a (paramNodes a t) hp = t := by
      apply paramNodes_injective a
      exact (chosenTuple_spec a (paramNodes a t) hp).trans rfl
    simp [hchosen]
  next hp =>
    exfalso
    apply hp
    exact ⟨t, rfl⟩

/-- The immediate child representation of every cover in the prefix tree. -/
theorem exists_child_of_covBy
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    ∃ t : ParamTuple arity a.level, ∃ c : Label,
      b = child a t c := by
  have hblev := LevelTree.covBy_level_eq hab
  rcases a with ⟨n, ha⟩
  change ∃ t : ParamTuple arity n, ∃ c : Label,
      b = child (⟨n, ha⟩ : Node Label arity) t c
  rcases b with ⟨m, hb⟩
  change m = n + 1 at hblev
  subst m
  let pc := historySuccEquiv n hb
  let bp : Node Label arity := ⟨n, pc.1⟩
  have hbp_le : bp ≤ (⟨n + 1, hb⟩ : Node Label arity) := by
    change Prefix pc.1 hb
    have hstep :
        History.step pc.1 pc.2 = hb :=
      (historySuccEquiv n).symm_apply_apply hb
    rw [← hstep]
    exact Prefix.step (Prefix.refl _) pc.2
  have ha_le : (⟨n, ha⟩ : Node Label arity) ≤
      (⟨n + 1, hb⟩ : Node Label arity) :=
    hab.le
  have habp : (⟨n, ha⟩ : Node Label arity) = bp := by
    rcases node_lower_linear ha_le hbp_le with h | h
    · exact node_eq_of_le_level_eq h rfl
    · exact (node_eq_of_le_level_eq h rfl).symm
  have hparent : ha = pc.1 := by
    simpa only [bp, Sigma.mk.inj_iff, heq_eq_eq, true_and] using habp
  have hstep :
      History.step pc.1 pc.2 = hb :=
    (historySuccEquiv n).symm_apply_apply hb
  rcases hcode : pc.2 with ⟨c, t⟩
  refine ⟨t, c, ?_⟩
  have hhist : hb = History.step ha ⟨c, t⟩ := by
    rw [← hstep, ← hparent, hcode]
  change (⟨n + 1, hb⟩ : Node Label arity) =
    ⟨n + 1, History.step ha ⟨c, t⟩⟩
  rw [hhist]

theorem freeSucc_s3
    {a b : Node Label arity}
    (hab : a ⋖ b) :
    ∃ p : List (Node Label arity), ∃ c : Label,
      freeSucc a p c = some b := by
  obtain ⟨t, c, rfl⟩ := exists_child_of_covBy hab
  exact ⟨paramNodes a t, c, freeSucc_paramNodes a t c⟩

theorem freeSucc_s1
    {a b : Node Label arity}
    {p : List (Node Label arity)}
    {c : Label}
    (h : freeSucc a p c = some b) :
    a ⋖ b ∧
      ∀ x ∈ p, LevelTree.lev x < LevelTree.lev a := by
  obtain ⟨t, htp, rfl⟩ := freeSucc_eq_some_data h
  refine ⟨base_covBy_child a t c, ?_⟩
  intro x hx
  apply mem_paramNodes_level_lt (t := t)
  simpa [htp] using hx

/-- The free ancestral successor tree. -/
noncomputable def freeSTree :
    STree (Node Label arity) Label where
  succ := freeSucc
  s1 := freeSucc_s1
  s2 := freeSucc_s2
  s3 := freeSucc_s3

end FreeAncestral
end SuccessorTree
