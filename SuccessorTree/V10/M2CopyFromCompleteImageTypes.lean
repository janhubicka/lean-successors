import SuccessorTree.V10.M2ImageOrdinaryZone
import SuccessorTree.V10.M2CopyImageTransfer
import SuccessorTree.V10.PrescribedCorrectedB3
import Mathlib.Tactic

/-!
# The induced forbidden-copy assembly from complete image parameters

The four binary zones split at the inserted coordinate m. Complete
image parameter types give both directed lower--upper atoms; the
common initial socle gives the lower--lower atoms; the retained-record
source pullback gives upper--upper atoms. This lemma checks the exact
induced embedding, including negative directed atoms and singleton data.
-/
namespace SuccessorTree.V10

/-- The exact finite-pattern transfer from the three genuinely independent
record sources. The image types cover the gap coordinate itself. -/
theorem m2ForbiddenCopy_from_complete_upper_types
    {N r db du dd : Nat}
    (Q : PartialTypeWithE N db du dd)
    (W : AgeTestModel db du dd)
    (lambda : Nat → Nat) (n m : Nat) (e : Fin r → Nat)
    (hLambda : StrictMono lambda) (hGap : m < lambda n)
    (hInitial : SameInitialL Q.ageModel W m)
    (hUpper : ∀ (a : Fin r) (ha : m < e a),
      ∃ (hj : lambda (NonedgePadding.address n (n+a.val)) < N)
        (hq : m+1 ≤ N),
        (Q.ordinaryType (lambda (NonedgePadding.address n (n+a.val)))
          hj (m+1) hq).lReduct =
            RelationalPrefixType.ofAgeModel W (m+1) (e a))
    (hHighHigh : ∀ (a b : Fin r), m < e a → m < e b →
      ∀ t : Fin db,
        Q.ageModel.binary
          (lambda (NonedgePadding.address n (n+a.val)))
          (lambda (NonedgePadding.address n (n+b.val))) t =
            W.binary (e a) (e b) t)
    (P : ForbiddenAtomicPattern r db du dd)
    (hCopy : W.Realizes P e) :
    Q.ageModel.Realizes P (m2ForbiddenCopyImage lambda n m r e) := by
  have hZone (a : Fin r) (ha : m < e a) :
      (∀ (k : Nat) (hk : k < m+1) (t : Fin db),
        Q.ageModel.binary k
          (lambda (NonedgePadding.address n (n+a.val))) t =
            W.binary k (e a) t ∧
        Q.ageModel.binary
          (lambda (NonedgePadding.address n (n+a.val))) k t =
            W.binary (e a) k t) ∧
      (∀ t : Fin db,
        Q.ageModel.binary
          (lambda (NonedgePadding.address n (n+a.val)))
          (lambda (NonedgePadding.address n (n+a.val))) t =
            W.binary (e a) (e a) t) ∧
      (∀ t : Fin du,
        Q.ageModel.unary
          (lambda (NonedgePadding.address n (n+a.val))) t =
            W.unary (e a) t) ∧
      (∀ t : Fin dd,
        Q.ageModel.diagonal
          (lambda (NonedgePadding.address n (n+a.val))) t =
            W.diagonal (e a) t) := by
    obtain ⟨hj,hq,hType⟩ := hUpper a ha
    exact image_ordinary_type_all_low_upper_atoms
      Q (lambda (NonedgePadding.address n (n+a.val))) hj hq W (e a) hType
  have hInside : ∀ a : Fin r,
      m2ForbiddenCopyImage lambda n m r e a ∈ Q.ageModel.carrier := by
    intro a
    by_cases ha : e a ≤ m
    · rw [m2ForbiddenCopyImage_lower lambda n m r e a ha]
      exact (hInitial.1 (e a) ha).2 (hCopy.2.1 a)
    · have ha' : m < e a := by omega
      obtain ⟨hj,_hq,_htype⟩ := hUpper a ha'
      rw [m2ForbiddenCopyImage_upper lambda n m r e a ha']
      change lambda (NonedgePadding.address n (n+a.val)) ≤ N
      omega
  have hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      Q.ageModel.binary (m2ForbiddenCopyImage lambda n m r e a)
        (m2ForbiddenCopyImage lambda n m r e b) t =
        W.binary (e a) (e b) t := by
    apply m2ForbiddenCopy_binary_of_zones W Q.ageModel lambda n m e
    · intro a b _hab ha hb t
      exact hInitial.2.1 (e a) (e b) ha hb t
    · intro a b _hab ha hb t
      exact (hZone b hb).1 (e a) (by omega) t |>.1
    · intro a b _hab ha hb t
      exact (hZone a ha).1 (e b) (by omega) t |>.2
    · intro a b _hab ha hb t
      exact hHighHigh a b ha hb t
  have hUnary : ∀ a : Fin r, ∀ t : Fin du,
      Q.ageModel.unary (m2ForbiddenCopyImage lambda n m r e a) t =
        W.unary (e a) t := by
    intro a t
    by_cases ha : e a ≤ m
    · rw [m2ForbiddenCopyImage_lower lambda n m r e a ha]
      exact hInitial.2.2.1 (e a) ha t
    · have ha' : m < e a := by omega
      rw [m2ForbiddenCopyImage_upper lambda n m r e a ha']
      exact (hZone a ha').2.2.1 t
  have hDiagonal : ∀ a : Fin r, ∀ t : Fin dd,
      Q.ageModel.diagonal (m2ForbiddenCopyImage lambda n m r e a) t =
        W.diagonal (e a) t := by
    intro a t
    by_cases ha : e a ≤ m
    · rw [m2ForbiddenCopyImage_lower lambda n m r e a ha]
      exact hInitial.2.2.2 (e a) ha t
    · have ha' : m < e a := by omega
      rw [m2ForbiddenCopyImage_upper lambda n m r e a ha']
      exact (hZone a ha').2.2.2 t
  exact m2ForbiddenCopy_realizes_of_atomwise P W Q.ageModel
    lambda n m e hLambda hGap hCopy hInside hBinary hUnary hDiagonal

end SuccessorTree.V10
