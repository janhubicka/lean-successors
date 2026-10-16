import SuccessorTree.FreeAncestralSMTree
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Tactic

/-!
# Encoding the pure free-ancestral monoid by Cantor space

The free-ancestral tree has countably many vertices (each individual
level is finite, with a vertex at every natural-number level).
A total shape-preserving map is determined by its underlying function,
so at most continuum many such maps exist.

Consequently the pure monoid maps -- those fixing levels 0 and 1
pointwise -- have a surjective enumeration by binary sequences.
Combined with \`BinarySupports.lean\` and \`GreedySelection.lean\`,
this permits a ZFC transfinite schedule of **every** pure refinement.
-/

namespace SuccessorTree.Counterexample

open SuccessorTree.FreeAncestral

/-- Countability of the underlying free-ancestral node type. -/
noncomputable instance freeNodeCountable :
    Countable (Node Unit 1) := by
  change Countable (Sigma (History Unit 1))
  infer_instance

/-- Every natural depth has an explicitly named node. -/
noncomputable instance freeNodeInfinite :
    Infinite (Node Unit 1) := by
  let e : ℕ ↪ Node Unit 1 :=
    ⟨fun n => canonicalNode (Label := Unit) (arity := 1) n, by
      intro i j hij
      have h := congrArg Node.level hij
      simpa using h⟩
  exact Infinite.of_injective e e.injective

theorem freeNode_cardinality :
    Cardinal.mk (Node Unit 1) = Cardinal.aleph0 :=
  Cardinal.mk_eq_aleph0 _

/-- The cardinality of all functions from this countable free tree to
itself is the continuum. -/
theorem freeNode_functions_cardinality :
    Cardinal.mk (Node Unit 1 → Node Unit 1) =
      Cardinal.continuum := by
  rw [Cardinal.mk_arrow]
  simp [freeNode_cardinality, Cardinal.aleph0_power_aleph0]

/-- The binary-function space is exactly the continuum. -/
theorem cantorFunction_cardinality :
    Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
  rw [Cardinal.mk_arrow]
  simp [Cardinal.continuum]

/-- The entire distinguished full free-ancestral shape-map monoid
has at most continuum many elements. -/
theorem freeMMap_card_le_cantor :
    Cardinal.mk (SuccessorTree.SMTree.MMap
      (freeSMTree (Label := Unit) (arity := 1))) ≤
        Cardinal.mk (ℕ → Bool) := by
  let H := freeSMTree (Label := Unit) (arity := 1)
  let encode : SuccessorTree.SMTree.MMap H ↪
      (Node Unit 1 → Node Unit 1) :=
    ⟨fun F x => F x, by
      intro F G hFG
      apply SuccessorTree.SMTree.MMap.ext_apply
      intro x
      exact congrFun hFG x⟩
  have hcard : Cardinal.mk (SuccessorTree.SMTree.MMap H) ≤
      Cardinal.mk (Node Unit 1 → Node Unit 1) :=
    Cardinal.mk_le_of_injective encode.injective
  calc
    Cardinal.mk (SuccessorTree.SMTree.MMap H) ≤
        Cardinal.mk (Node Unit 1 → Node Unit 1) := hcard
    _ = Cardinal.continuum := freeNode_functions_cardinality
    _ = Cardinal.mk (ℕ → Bool) := cantorFunction_cardinality.symm

/-- Pure maps fix **both** source levels zero and one. In the manuscript's
level-based notation these constitute [1,Id], with the corresponding
approximation-space index equal to two. -/
def PureFreeMap : Type :=
  {H : SuccessorTree.SMTree.MMap
      (freeSMTree (Label := Unit) (arity := 1)) //
    ∀ x : Node Unit 1, x.level ≤ 1 → H x = x}

noncomputable def pureFreeIdentity : PureFreeMap :=
  ⟨SuccessorTree.SMTree.MMap.id
      (freeSMTree (Label := Unit) (arity := 1)), by
    intro x _
    rfl⟩

theorem pureFree_card_le_cantor :
    Cardinal.mk PureFreeMap ≤ Cardinal.mk (ℕ → Bool) := by
  have hsub :
      Cardinal.mk PureFreeMap ≤
        Cardinal.mk (SuccessorTree.SMTree.MMap
          (freeSMTree (Label := Unit) (arity := 1))) :=
    Cardinal.mk_le_of_injective (Subtype.val_injective)
  exact hsub.trans freeMMap_card_le_cantor

/-- A choice-free *existence statement* (although selecting an enumeration
uses classical choice): every pure shape-map refinement is scheduled by
some infinite binary sequence. The construction does not require CH. -/
theorem exists_pureFree_enumeration :
    ∃ schedule : (ℕ → Bool) → PureFreeMap,
      Function.Surjective schedule := by
  classical
  obtain ⟨emb⟩ : Nonempty (PureFreeMap ↪ (ℕ → Bool)) :=
    pureFree_card_le_cantor
  let schedule : (ℕ → Bool) → PureFreeMap := fun b =>
    if hb : ∃ H : PureFreeMap, emb H = b then
      Classical.choose hb
    else pureFreeIdentity
  refine ⟨schedule, ?_⟩
  intro H
  refine ⟨emb H, ?_⟩
  have hb : ∃ G : PureFreeMap, emb G = emb H := ⟨H, rfl⟩
  change (if h : ∃ G : PureFreeMap, emb G = emb H then
    Classical.choose h else pureFreeIdentity) = H
  rw [dif_pos hb]
  exact emb.injective (Classical.choose_spec hb)

end SuccessorTree.Counterexample
