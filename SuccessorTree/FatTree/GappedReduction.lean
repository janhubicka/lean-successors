import SuccessorTree.FatTree.GappedBasic

/-!
# The actual geometric reduction of whole gapped lines

A gapped line is an entire width-two finite approximation with a
distinguished internal level and a right cutting mark. The lift itself
is the old formula: canonical extension of the whole row applied to
all immediate successors of the starting cut.

We use an all-interval lift inclusion in the reduction record.
This is a transparent geometric condition, not algebraic
right-composition and not merely two index embeddings. The
one-step/infinite-interval equivalence requires source locality and
belongs to a subsequent lemma.

No A4 or Ramsey conclusion is a field of the definition.
-/

namespace SuccessorTree
namespace SMTree
namespace FatTree

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}
variable {H : SMTree S}

namespace GappedFatTree

/-- Lift through consecutive whole-variable rows. -/
noncomputable def liftSteps (U : GappedFatTree H) :
    (i steps : Nat) → Set T → Set T
  | _, 0, X => X
  | i, steps + 1, X =>
      liftSteps U (i+1) steps (U.oneLift i X)

@[simp] theorem liftSteps_zero (U : GappedFatTree H)
    (i : Nat) (X : Set T) :
    U.liftSteps i 0 X = X := rfl

@[simp] theorem liftSteps_succ (U : GappedFatTree H)
    (i steps : Nat) (X : Set T) :
    U.liftSteps i (steps+1) X =
      U.liftSteps (i+1) steps (U.oneLift i X) := rfl

theorem oneLift_mono (U : GappedFatTree H) (i : Nat)
    {X Y : Set T} (hXY : X ⊆ Y) :
    U.oneLift i X ⊆ U.oneLift i Y := by
  intro z hz
  rcases hz with ⟨w, hw, rfl⟩
  exact ⟨w, FatTree.immediateSuccessors_mono H hXY hw, rfl⟩

theorem liftSteps_mono (U : GappedFatTree H)
    (i steps : Nat) {X Y : Set T} (hXY : X ⊆ Y) :
    U.liftSteps i steps X ⊆ U.liftSteps i steps Y := by
  induction steps generalizing i X Y with
  | zero => exact hXY
  | succ steps ih =>
      exact ih (i := i+1)
        (X := U.oneLift i X) (Y := U.oneLift i Y)
        (U.oneLift_mono i hXY)

theorem liftSteps_add (U : GappedFatTree H)
    (i a b : Nat) (X : Set T) :
    U.liftSteps i (a+b) X =
      U.liftSteps (i+a) b (U.liftSteps i a X) := by
  induction a generalizing i X with
  | zero => simp
  | succ a ih =>
      rw [Nat.succ_add, liftSteps_succ, liftSteps_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (i:=i+1) (X:=U.oneLift i X)

/-- Source- and destination-indexed whole-line lift. -/
noncomputable def liftTo (U : GappedFatTree H)
    (i j : Nat) (hij : i ≤ j) (X : Set T) : Set T :=
  U.liftSteps i (j-i) X

theorem liftTo_refl (U : GappedFatTree H) (i : Nat) (X : Set T) :
    U.liftTo i i le_rfl X = X := by simp [liftTo]

theorem liftTo_split (U : GappedFatTree H)
    (i j k : Nat) (hij : i ≤ j) (hjk : j ≤ k) (X : Set T) :
    U.liftTo i k (hij.trans hjk) X =
      U.liftTo j k hjk (U.liftTo i j hij X) := by
  change U.liftSteps i (k-i) X =
    U.liftSteps j (k-j) (U.liftSteps i (j-i) X)
  have hsum : k-i=(j-i)+(k-j) := by omega
  have hidx : i+(j-i)=j := by omega
  rw [hsum, U.liftSteps_add i (j-i) (k-j) X, hidx]

theorem liftTo_mono (U : GappedFatTree H)
    (i j : Nat) (hij : i ≤ j)
    {X Y : Set T} (hXY : X ⊆ Y) :
    U.liftTo i j hij X ⊆ U.liftTo i j hij Y :=
  U.liftSteps_mono i (j-i) hXY

/-- Each marked lift lands at the right-hand cutting mark. -/
theorem liftSteps_subset_level (U : GappedFatTree H)
    (i steps : Nat) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.liftSteps i steps X ⊆
      TreeLevel (T := T) (U.cut (i+steps)) := by
  induction steps generalizing i X with
  | zero => simpa using hX
  | succ steps ih =>
      have hnext : U.oneLift i X ⊆
          TreeLevel (T := T) (U.cut (i+1)) :=
        U.oneLift_subset_right_cut i hX
      have hrec := ih (i:=i+1) (X:=U.oneLift i X) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

theorem liftTo_subset_level (U : GappedFatTree H)
    (i j : Nat) (hij : i ≤ j) {X : Set T}
    (hX : X ⊆ TreeLevel (T := T) (U.cut i)) :
    U.liftTo i j hij X ⊆ TreeLevel (T := T) (U.cut j) := by
  have h := U.liftSteps_subset_level i (j-i) hX
  simpa [liftTo, show i+(j-i)=j by omega] using h

/-- One all-interval inclusion for each ambient marked line interval.
This is the mathematically literal geometric reduction and ensures
transitivity without a hidden algebraic factorisation. -/
structure ReductionWitness (V U : GappedFatTree H) where
  index : Nat → Nat
  index_strict : StrictMono index
  cut_eq : ∀ i, V.cut i = U.cut (index i)
  lift_subset : ∀ i j (hij : i ≤ j),
    V.liftTo i j hij (TreeLevel (T := T) (V.cut i)) ⊆
    U.liftTo (index i) (index j)
      (index_strict.monotone hij)
      (TreeLevel (T := T) (U.cut (index i)))

def Reduces (V U : GappedFatTree H) : Prop :=
  Nonempty (ReductionWitness V U)

namespace ReductionWitness

theorem index_zero {V U : GappedFatTree H}
    (w : ReductionWitness V U) : w.index 0 = 0 := by
  apply (U.cut_strictMono).injective
  calc
    U.cut (w.index 0) = V.cut 0 := (w.cut_eq 0).symm
    _ = 0 := V.cut_zero
    _ = U.cut 0 := U.cut_zero.symm

def refl (U : GappedFatTree H) : ReductionWitness U U where
  index := id
  index_strict := strictMono_id
  cut_eq := fun _ => rfl
  lift_subset := by intro i j hij; exact Set.Subset.rfl

def trans {V U W : GappedFatTree H}
    (vU : ReductionWitness V U) (uW : ReductionWitness U W) :
    ReductionWitness V W where
  index := uW.index ∘ vU.index
  index_strict := uW.index_strict.comp vU.index_strict
  cut_eq := by
    intro i
    calc
      V.cut i = U.cut (vU.index i) := vU.cut_eq i
      _ = W.cut (uW.index (vU.index i)) := uW.cut_eq _
  lift_subset := by
    intro i j hij
    calc
      V.liftTo i j hij (TreeLevel (T := T) (V.cut i)) ⊆
        U.liftTo (vU.index i) (vU.index j)
          (vU.index_strict.monotone hij)
          (TreeLevel (T := T) (U.cut (vU.index i))) :=
        vU.lift_subset i j hij
      _ ⊆
        W.liftTo (uW.index (vU.index i)) (uW.index (vU.index j))
          (uW.index_strict.monotone (vU.index_strict.monotone hij))
          (TreeLevel (T := T) (W.cut (uW.index (vU.index i)))) :=
        uW.lift_subset _ _ (vU.index_strict.monotone hij)

end ReductionWitness

theorem reduces_refl (U : GappedFatTree H) : Reduces U U :=
  ⟨ReductionWitness.refl U⟩

theorem reduces_trans {V U W : GappedFatTree H}
    (hVU : Reduces V U) (hUW : Reduces U W) :
    Reduces V W := by
  obtain ⟨vU⟩ := hVU
  obtain ⟨uW⟩ := hUW
  exact ⟨ReductionWitness.trans vU uW⟩

end GappedFatTree
end FatTree
end SMTree
end SuccessorTree
