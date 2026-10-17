import Mathlib.Tactic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Choice-theoretic greedy selection from almost-disjoint candidates

The cardinal bookkeeping in the transfinite stage of the ZFC
Theorem 1.11 counterexample is entirely independent of successor trees.

At a stage i, each earlier object can forbid at most **one**
candidate indexed by α. If α does not embed into the strict
initial segment below i, then a candidate remains. A well-founded
recursion therefore constructs a family which has no conflicts
between any two distinct stages.

No continuum hypothesis or regularity of the continuum is needed:
the only size assumption is that every proper initial segment of
the chosen well-order is smaller than the full index type.
-/

namespace SuccessorTree.Counterexample

universe u v w

/-- Every forbidden index has a *different* witnessing earlier object;
otherwise uniqueness would force those indices to be equal. Thus if the
index type does not inject into the type of earlier stages, a candidate
is left. -/
theorem exists_candidate_avoiding
    {Index : Type u} {Past : Type v} {M : Type w}
    (candidate : Index → M) (previous : Past → M)
    (conflicts : M → M → Prop)
    (hunique : ∀ (g : M) (i j : Index),
      conflicts g (candidate i) → conflicts g (candidate j) → i = j)
    (hsmall : ¬ Nonempty (Index ↪ Past)) :
    ∃ i : Index, ∀ j : Past,
      ¬ conflicts (previous j) (candidate i) := by
  classical
  by_contra h
  have hall : ∀ i : Index, ∃ j : Past,
      conflicts (previous j) (candidate i) := by
    intro i
    by_contra hi
    apply h
    refine ⟨i, ?_⟩
    intro j hj
    exact hi ⟨j, hj⟩
  let f : Index → Past := fun i => Classical.choose (hall i)
  have hf : ∀ i : Index,
      conflicts (previous (f i)) (candidate i) :=
    fun i => Classical.choose_spec (hall i)
  have hinj : Function.Injective f := by
    intro i j hij
    have hj : conflicts (previous (f i)) (candidate j) := by
      simpa only [hij] using hf j
    exact hunique (previous (f i)) i j (hf i) hj
  exact hsmall ⟨⟨f, hinj⟩⟩

section Greedy

variable {Index : Type u} {M : Type v}
variable [LinearOrder Index]
variable (wf : WellFounded (fun a b : Index => a < b))
variable (candidates : Index → Index → M)
variable (conflicts : M → M → Prop)
variable (hunique : ∀ (stage : Index) (g : M) (i j : Index),
  conflicts g (candidates stage i) →
  conflicts g (candidates stage j) → i = j)
variable (hsmall : ∀ stage : Index,
  ¬ Nonempty (Index ↪ {j : Index // j < stage}))

/-- At each transfinite stage, choose an index not forbidden by an
earlier selected object. The function \`previous\` can be arbitrary. -/
noncomputable def nextIndex (stage : Index)
    (previous : ∀ j : Index, j < stage → M) : Index :=
  Classical.choose
    (exists_candidate_avoiding
      (candidates stage)
      (fun j : {j : Index // j < stage} => previous j.1 j.2)
      conflicts
      (hunique stage)
      (hsmall stage))

theorem nextIndex_spec (stage : Index)
    (previous : ∀ j : Index, j < stage → M) :
    ∀ (j : Index) (hj : j < stage),
      ¬ conflicts (previous j hj)
        (candidates stage
          (nextIndex candidates conflicts hunique hsmall stage previous)) := by
  intro j hj
  exact (Classical.choose_spec
    (exists_candidate_avoiding
      (candidates stage)
      (fun k : {k : Index // k < stage} => previous k.1 k.2)
      conflicts (hunique stage) (hsmall stage))) ⟨j, hj⟩

/-- ZFC greedy antichain selection, recursively following an initial
well-order of the size of the candidate-support family. -/
noncomputable def greedySelection : Index → M :=
  wf.fix (fun stage previous =>
    candidates stage
      (nextIndex candidates conflicts hunique hsmall stage
        (fun j hj => previous j hj)))

theorem greedySelection_step (stage : Index) :
    greedySelection wf candidates conflicts hunique hsmall stage =
      candidates stage
        (nextIndex candidates conflicts hunique hsmall stage
          (fun j _ => greedySelection wf candidates conflicts hunique hsmall j)) := by
  unfold greedySelection
  rw [WellFounded.fix_eq]

/-- Every stage is incompatible with all earlier stages, without
any regularity assumption on the length of the well-order. -/
theorem greedySelection_avoids_earlier
    (stage j : Index) (hj : j < stage) :
    ¬ conflicts
      (greedySelection wf candidates conflicts hunique hsmall j)
      (greedySelection wf candidates conflicts hunique hsmall stage) := by
  rw [greedySelection_step wf candidates conflicts hunique hsmall stage]
  exact nextIndex_spec candidates conflicts hunique hsmall stage
    (fun k _ => greedySelection wf candidates conflicts hunique hsmall k) j hj

/-- The chosen object at stage i genuinely belongs to the
candidate family indexed by that stage. -/
theorem greedySelection_is_candidate (stage : Index) :
    ∃ i : Index,
      greedySelection wf candidates conflicts hunique hsmall stage =
        candidates stage i := by
  exact ⟨nextIndex candidates conflicts hunique hsmall stage
    (fun j _ => greedySelection wf candidates conflicts hunique hsmall j),
      greedySelection_step wf candidates conflicts hunique hsmall stage⟩

/-- Symmetry of compatibility turns the earlier-stage condition
into full pairwise incompatibility. -/
theorem greedySelection_pairwise
    (hsymm : ∀ a b : M, conflicts a b → conflicts b a)
    {i j : Index} (hij : i ≠ j) :
    ¬ conflicts
      (greedySelection wf candidates conflicts hunique hsmall i)
      (greedySelection wf candidates conflicts hunique hsmall j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · intro h
    exact (greedySelection_avoids_earlier wf candidates conflicts
      hunique hsmall j i hlt) h
  · intro h
    exact (greedySelection_avoids_earlier wf candidates conflicts
      hunique hsmall i j hgt) (hsymm _ _ h)

end Greedy

/-!
## Minimal-ordinal schedules

The abstract smaller-initial-segment assumption above is automatic
when the well-order on the stage type has the **least ordinal**
of that cardinality. The result is exactly why the greedy argument
does not need CH or regularity of the continuum.
-/

/-- Every strict initial segment of a well-order of minimal ordinal
type has strictly smaller cardinality; hence the full index type
cannot inject into it. -/
theorem no_embedding_earlier_of_minimal_ord
    {Index : Type u} [LinearOrder Index] [WellFoundedLT Index]
    (hminimal : Cardinal.ord (Cardinal.mk Index) =
      Ordinal.type (fun i j : Index => i < j))
    (stage : Index) :
    ¬ Nonempty (Index ↪ {j : Index // j < stage}) := by
  intro he
  obtain ⟨f⟩ := he
  have hle :
      Cardinal.mk Index ≤ Cardinal.mk {j : Index // j < stage} :=
    Cardinal.mk_le_of_injective f.injective
  have hordinal :
      Ordinal.typein (fun i j : Index => i < j) stage <
        Cardinal.ord (Cardinal.mk Index) := by
    rw [hminimal]
    exact Ordinal.typein_lt_type _ stage
  have hsmall :
      Cardinal.mk {j : Index // j < stage} <
        Cardinal.mk Index := by
    have hh := Cardinal.lt_ord.mp hordinal
    simpa only [Ordinal.card_typein] using hh
  exact (not_le_of_gt hsmall) hle


end SuccessorTree.Counterexample
