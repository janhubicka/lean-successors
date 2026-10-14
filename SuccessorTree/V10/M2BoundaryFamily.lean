import SuccessorTree.V10.PrescribedBoringData
import Mathlib.Tactic

/-!
# Package an injectively indexed family as genuine B1/B2 data

The source family is the range of the embedded prescribed source types.
The prescribed value of each member is exactly its indexed output.
This is useful for the intrinsic deletion D and the original F when
B1/B2 have been established on boundary-indexed admissible Kpt nodes.
Nothing is assumed or proved about CompatibleB3.
-/

namespace SuccessorTree.V10

/-- Neutral dummy value, used only outside the intended prescription. -/
def PartialTypeWithE.neutral (n db du dd : Nat) : PartialTypeWithE n db du dd :=
  { lReduct :=
      { binary := fun _ _ _ => false
        unary := fun _ _ => false
        diagonal := fun _ _ => false }
    eRelation := fun _ _ => false }

/-- Build the actual B1/B2 record from injectively indexed finite-cut
source and target type families. Injectivity is needed only for the
source indexing. No B3 hypothesis is hidden in the constructor. -/
noncomputable def PrescribedBoringData.ofInjective
    {ell db du dd : Nat} {α : Type*}
    (s : α → PartialTypeWithE ell db du dd)
    (t : α → PartialTypeWithE (ell+1) db du dd)
    (hinj : Function.Injective s)
    (hB1 : ∀ a, (t a).restrict (Nat.le_succ ell) = s a)
    (hB2 : ∀ a b, SameOrdinaryAtCut (s a) (s b) →
      SameOrdinarySocle (t a) (t b)) :
    PrescribedBoringData ell db du dd := by
  classical
  let v (Q : PartialTypeWithE ell db du dd) :=
    if h : Q ∈ Set.range s then t (Classical.choose h)
    else PartialTypeWithE.neutral (ell+1) db du dd
  have hv (a : α) : v (s a) = t a := by
    have h : s a ∈ Set.range s := ⟨a,rfl⟩
    have hChosen : s (Classical.choose h) = s a :=
      Classical.choose_spec h
    simp only [v, dite_eq_left h]
    exact congrArg t (hinj hChosen)
  exact {
    source := Set.range s
    target := v
    extendsSource := by
      intro Q hQ
      rcases hQ with ⟨a,rfl⟩
      rw [hv a]
      exact hB1 a
    preservesCompatibility := by
      intro Q R hQ hR hComp
      rcases hQ with ⟨a,rfl⟩
      rcases hR with ⟨b,rfl⟩
      rw [hv a, hv b]
      exact hB2 a b hComp
  }

/-- Representative choice does not affect the prescribed target. -/
theorem PrescribedBoringData.ofInjective_target
    {ell db du dd : Nat} {α : Type*}
    (s : α → PartialTypeWithE ell db du dd)
    (t : α → PartialTypeWithE (ell+1) db du dd)
    (hinj : Function.Injective s)
    (hB1 : ∀ a, (t a).restrict (Nat.le_succ ell) = s a)
    (hB2 : ∀ a b, SameOrdinaryAtCut (s a) (s b) →
      SameOrdinarySocle (t a) (t b)) (a : α) :
    (PrescribedBoringData.ofInjective s t hinj hB1 hB2).target (s a) = t a := by
  classical
  unfold PrescribedBoringData.ofInjective
  simp only
  generalize hP : (fun Q : PartialTypeWithE ell db du dd =>
    if h : Q ∈ Set.range s then t (Classical.choose h)
    else PartialTypeWithE.neutral (ell+1) db du dd) = v
  have h : s a ∈ Set.range s := ⟨a,rfl⟩
  have hChosen : s (Classical.choose h) = s a := Classical.choose_spec h
  simpa [hP] using congrArg t (hinj hChosen)

end SuccessorTree.V10
