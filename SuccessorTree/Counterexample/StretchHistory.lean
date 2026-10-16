import SuccessorTree.Counterexample.MaskCodes
import Mathlib.Tactic

/-!
# Explicit infinite masked history maps

The underlying function of the counterexample map \`Q_A\` is constructed
*directly* on every finite free-ancestral history using a strictly
increasing map \`levels : ℕ → ℕ\` with \`levels 0 = 1\`.

A source edge receives a mandatory successor code whose ancestral
parameter indices k are sent to levels k. Every additional target
edge up to the next retained level receives the **root marker**
(code with the single ancestral parameter at target level zero).

The present module isolates the dependent indexed-history construction.
A later module proves injectivity, order/weak-successor preservation,
and the resulting \`ShapeMap\` structure.
-/

namespace SuccessorTree.FreeAncestral

/-- The sole legal code at the original root level. -/
def initialEmptyCode : Code Unit 1 0 :=
  ⟨(), emptyParamTuple 1 0⟩

/-- Append exactly k steps with the root as the unique ancestral
parameter. The positive starting level guarantees that the root is
a valid ancestor at every appended step. -/
def appendRootMarkers (n : Nat) (hn : 0 < n) :
    (k : Nat) → History Unit 1 n → History Unit 1 (n + k)
  | 0, h => h
  | k + 1, h =>
      History.step (appendRootMarkers n hn k h)
        (rootMarkerCode (n + k) (by omega))

/-- The original history is always a prefix of its inserted
root-marker tail. -/
theorem prefix_appendRootMarkers
    (n : Nat) (hn : 0 < n) (k : Nat)
    (h : History Unit 1 n) :
    Prefix h (appendRootMarkers n hn k h) := by
  induction k with
  | zero =>
      exact Prefix.refl h
  | succ k ih =>
      exact Prefix.step ih
        (rootMarkerCode (n + k) (by omega))

/-- The root-marker padding is injective on starting histories. -/
theorem appendRootMarkers_injective
    (n : Nat) (hn : 0 < n) :
    ∀ k, Function.Injective (appendRootMarkers n hn k)
  | 0 => by
      intro a b hab
      exact hab
  | k + 1 => by
      intro a b hab
      apply appendRootMarkers_injective n hn k
      have hp :
          parent (appendRootMarkers n hn (k + 1) a) =
            parent (appendRootMarkers n hn (k + 1) b) :=
        congrArg parent hab
      exact hp

/-- Exact proof-relevant realization of the masked level embedding
on histories. The only use of choice is already in the shared
Lean library; the construction itself is ordinary dependent recursion. -/
noncomputable def markedHistoryAux
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    (n : Nat) → History Unit 1 n → History Unit 1 (levels n)
  | 0, h => by
      have hz : h = History.root := history_zero_unique h
      subst h
      simpa only [hroot] using
        (History.step History.root
          (initialEmptyCode) : History Unit 1 1)
  | n + 1, h => by
      cases h with
      | step p c =>
          let base : History Unit 1 (levels n) :=
            markedHistoryAux levels mono hroot n p
          let mandatory : History Unit 1 (levels n + 1) :=
            History.step base (remapCode levels mono c)
          have hle : levels n + 1 ≤ levels (n + 1) :=
            mono (Nat.lt_succ_self n)
          let gap : Nat := levels (n + 1) - (levels n + 1)
          have hsum : (levels n + 1) + gap = levels (n + 1) :=
            Nat.add_sub_of_le hle
          exact hsum ▸
            appendRootMarkers (levels n + 1) (by omega) gap mandatory

/-- The masked maps on the total node type. Their level map is literally
\`levels\`; packaging them as shape maps is the next theorem. -/
noncomputable def markedNode
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) (x : Node Unit 1) : Node Unit 1 :=
  ⟨levels x.level, markedHistoryAux levels mono hroot x.level x.2⟩

@[simp] theorem markedNode_level
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) (x : Node Unit 1) :
    (markedNode levels mono hroot x).level = levels x.level := rfl

/-- Changing the dependent history index in a sigma pair does
not change the represented total node. -/
private theorem totalNode_cast
    {a b : Nat} (hab : a = b) (x : History Unit 1 b) :
    (⟨a, hab.symm ▸ x⟩ : Node Unit 1) = ⟨b, x⟩ := by
  cases hab
  rfl

/-- Root image is precisely the empty-code child at target level one. -/
theorem markedNode_root
    (levels : Nat → Nat) (mono : StrictMono levels)
    (hroot : levels 0 = 1) :
    markedNode levels mono hroot (rootNode (Label := Unit) (arity := 1)) =
    (⟨1, History.step History.root initialEmptyCode⟩ : Node Unit 1) := by
  change (⟨levels 0, markedHistoryAux levels mono hroot 0 History.root⟩ :
      Node Unit 1) =
    ⟨1, History.step History.root initialEmptyCode⟩
  have haux :
      markedHistoryAux levels mono hroot 0 History.root =
        hroot.symm ▸ (History.step History.root initialEmptyCode :
          History Unit 1 1) := by
    rfl
  calc
    (⟨levels 0, markedHistoryAux levels mono hroot 0 History.root⟩ :
        Node Unit 1) =
        ⟨levels 0, hroot.symm ▸
          (History.step History.root initialEmptyCode : History Unit 1 1)⟩ := by
          rw [haux]
    _ = _ := totalNode_cast hroot _

end SuccessorTree.FreeAncestral
