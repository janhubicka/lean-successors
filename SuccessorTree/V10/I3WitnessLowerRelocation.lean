import SuccessorTree.V10.I3NumericRelocation
import SuccessorTree.V10.HFinitePartial
import Mathlib.Tactic

/-!
# Full lower--lower and singleton zones of the actual I3 relocation

Let W be an arbitrary finite L-only age witness with the exact
numerical H ordinary socle through ell. Its lower forbidden-copy
vertices are actual real H positions iota(first(a),generation(a))
listed by strictly increasing base first indices.

If the copy is irreducible, every two distinct lower vertices
are linked in W. We therefore may replace their generations
by their positions a=0,...,r-1, obtaining a strictly increasing
copy still below ell. Every directed lower--lower Boolean atom
and all unary/diagonal singleton data remain identical, including
absent tuples, and each relocated vertex belongs to W's carrier.

This is precisely the lower-zone lemma used in the author's
generation-relocation argument. The lower--upper and unchanged
upper--upper zones are treated separately. No E on W.
-/

namespace SuccessorTree.V10

/-- Full lower-zone transport inside an actual I3 age witness.
The old position of the last lower vertex is exactly ell, and
the contradiction branch assumes generation(last)>r-1.
Real first-index strictness, numerical representation and positive
links are the concrete facts obtained from irreducibility and
the exact H construction in the preceding proof modules. -/
theorem numericI3_lower_zone_relocation
    {db du dd : Nat}
    (K : AgeTestModel db du dd)
    (k N ell r : Nat) (hr : 0 < r) (hrk : r ≤ k)
    (W : AgeTestModel db du dd)
    (hSocle : SameInitialL W (finiteNumericHL K k N) ell)
    (hEllCarrier : ell ∈ W.carrier)
    (first generation : Fin r → Nat)
    (hFirst : StrictMono first)
    (hOld : ∀ a : Fin r,
      generation a ≤ k ∧
      hPosition k (first a) (generation a) ≤ ell)
    (hLast : ell = hPosition k
      (first ⟨r-1, by omega⟩) (generation ⟨r-1, by omega⟩))
    (hGap : r-1 < generation ⟨r-1, by omega⟩)
    (hLinked : ∀ a b : Fin r, a < b →
      ∃ t : Fin db,
        W.binary
          (hPosition k (first a) (generation a))
          (hPosition k (first b) (generation b)) t = true ∨
        W.binary
          (hPosition k (first b) (generation b))
          (hPosition k (first a) (generation a)) t = true) :
    let old : Fin r → Nat := fun a =>
      hPosition k (first a) (generation a)
    let relocated : Fin r → Nat := fun a =>
      hPosition k (first a) a.val
    (∀ a : Fin r, relocated a < ell ∧ relocated a ∈ W.carrier) ∧
    StrictMono relocated ∧
    (∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      W.binary (old a) (old b) t =
        W.binary (relocated a) (relocated b) t) ∧
    (∀ a : Fin r, ∀ t : Fin du,
      W.unary (old a) t = W.unary (relocated a) t) ∧
    (∀ a : Fin r, ∀ t : Fin dd,
      W.diagonal (old a) t = W.diagonal (relocated a) t) := by
  let old : Fin r → Nat := fun a =>
    hPosition k (first a) (generation a)
  let relocated : Fin r → Nat := fun a =>
    hPosition k (first a) a.val
  have hRankBound : ∀ a : Fin r, a.val ≤ k := by
    intro a
    have := a.isLt
    omega
  have hNewBelow : ∀ a : Fin r, relocated a < ell := by
    intro a
    change hPosition k (first a) a.val < ell
    rw [hLast]
    exact numericH_relocated_lower_before_old_last
      k r hr first generation hFirst hRankBound hGap a
  have hEllN : ell < N := by
    have h := (hSocle.1 ell (Nat.le_refl ell)).mp hEllCarrier
    change ell < N at h
    exact h
  have hNewCarrier : ∀ a : Fin r, relocated a ∈ W.carrier := by
    intro a
    apply (hSocle.1 (relocated a) (Nat.le_of_lt (hNewBelow a))).2
    change relocated a < N
    omega
  have hNewOrder : StrictMono relocated := by
    intro a b hab
    exact hPosition_lt_of_block_lt k
      (first a) (first b) a.val b.val
      (hRankBound a) (hFirst hab)
  have hPairs : ∀ a b : Fin r, a < b → ∀ t : Fin db,
      W.binary (old a) (old b) t =
        W.binary (relocated a) (relocated b) t ∧
      W.binary (old b) (old a) t =
        W.binary (relocated b) (relocated a) t := by
    intro a b hab t
    have hOldA : old a ≤ ell := (hOld a).2
    have hOldB : old b ≤ ell := (hOld b).2
    have hNumLink : ∃ s : Fin db,
        hNumericBinary K.binary k (old a) (old b) s = true ∨
        hNumericBinary K.binary k (old b) (old a) s = true := by
      obtain ⟨s,hAB | hBA⟩ := hLinked a b hab
      · exact ⟨s,Or.inl
          ((hSocle.2.1 (old a) (old b) hOldA hOldB s).symm.trans hAB)⟩
      · exact ⟨s,Or.inr
          ((hSocle.2.1 (old b) (old a) hOldB hOldA s).symm.trans hBA)⟩
    have hNumEq := numericH_linked_lower_lower_relocation
      K.binary k (first a) (first b)
      (generation a) (generation b) a.val b.val
      (hFirst hab) (Fin.lt_def.mp hab)
      (hRankBound b) (hOld a).1 (hOld b).1 hNumLink t
    constructor
    · calc
        W.binary (old a) (old b) t =
            hNumericBinary K.binary k (old a) (old b) t :=
          hSocle.2.1 (old a) (old b) hOldA hOldB t
        _ = hNumericBinary K.binary k
              (relocated a) (relocated b) t := hNumEq.1
        _ = W.binary (relocated a) (relocated b) t :=
          (hSocle.2.1 (relocated a) (relocated b)
            (Nat.le_of_lt (hNewBelow a))
            (Nat.le_of_lt (hNewBelow b)) t).symm
    · calc
        W.binary (old b) (old a) t =
            hNumericBinary K.binary k (old b) (old a) t :=
          hSocle.2.1 (old b) (old a) hOldB hOldA t
        _ = hNumericBinary K.binary k
              (relocated b) (relocated a) t := hNumEq.2
        _ = W.binary (relocated b) (relocated a) t :=
          (hSocle.2.1 (relocated b) (relocated a)
            (Nat.le_of_lt (hNewBelow b))
            (Nat.le_of_lt (hNewBelow a)) t).symm
  have hBinary : ∀ a b : Fin r, a ≠ b → ∀ t : Fin db,
      W.binary (old a) (old b) t =
        W.binary (relocated a) (relocated b) t := by
    intro a b hne t
    rcases lt_or_gt_of_ne hne with hab | hba
    · exact (hPairs a b hab t).1
    · exact (hPairs b a hba t).2
  have hUnary : ∀ a : Fin r, ∀ t : Fin du,
      W.unary (old a) t = W.unary (relocated a) t := by
    intro a t
    have hOldUnary : (finiteNumericHL K k N).unary (old a) t =
        K.unary (first a) t := by
      exact congrArg (fun f : Fin du → Bool => f t)
        (hNumericSingleton_real K.unary k (first a)
          (generation a) (hOld a).1)
    have hNewUnary : (finiteNumericHL K k N).unary (relocated a) t =
        K.unary (first a) t := by
      exact congrArg (fun f : Fin du → Bool => f t)
        (hNumericSingleton_real K.unary k (first a)
          a.val (hRankBound a))
    calc
      W.unary (old a) t =
          (finiteNumericHL K k N).unary (old a) t :=
        hSocle.2.2.1 (old a) (hOld a).2 t
      _ = K.unary (first a) t := hOldUnary
      _ = (finiteNumericHL K k N).unary (relocated a) t :=
        hNewUnary.symm
      _ = W.unary (relocated a) t :=
        (hSocle.2.2.1 (relocated a)
          (Nat.le_of_lt (hNewBelow a)) t).symm
  have hDiagonal : ∀ a : Fin r, ∀ t : Fin dd,
      W.diagonal (old a) t = W.diagonal (relocated a) t := by
    intro a t
    have hOldDiagonal : (finiteNumericHL K k N).diagonal (old a) t =
        K.diagonal (first a) t := by
      exact congrArg (fun f : Fin dd → Bool => f t)
        (hNumericSingleton_real K.diagonal k (first a)
          (generation a) (hOld a).1)
    have hNewDiagonal : (finiteNumericHL K k N).diagonal (relocated a) t =
        K.diagonal (first a) t := by
      exact congrArg (fun f : Fin dd → Bool => f t)
        (hNumericSingleton_real K.diagonal k (first a)
          a.val (hRankBound a))
    calc
      W.diagonal (old a) t =
          (finiteNumericHL K k N).diagonal (old a) t :=
        hSocle.2.2.2 (old a) (hOld a).2 t
      _ = K.diagonal (first a) t := hOldDiagonal
      _ = (finiteNumericHL K k N).diagonal (relocated a) t :=
        hNewDiagonal.symm
      _ = W.diagonal (relocated a) t :=
        (hSocle.2.2.2 (relocated a)
          (Nat.le_of_lt (hNewBelow a)) t).symm
  exact ⟨fun a => ⟨hNewBelow a,hNewCarrier a⟩,
    hNewOrder,hBinary,hUnary,hDiagonal⟩

end SuccessorTree.V10
