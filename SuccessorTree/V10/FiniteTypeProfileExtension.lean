import SuccessorTree.V10.FiniteTypeProfileInsertion
import SuccessorTree.V10.FiniteTypeProfileCloseGap

/-!
# Extending an intrinsic finite type profile

The proof reuses canonical gap closing and the existing compatible boring
extension. It proceeds through the finitely many source fronts, filling the
image gap above each previous front one coordinate at a time.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace FiniteTypeProfileMap

variable {A B : FiniteTypeBase family}

/-- Fill the remaining finite target gap at a prescribed source front. -/
theorem fill_front (h : FiniteTypeProfileMap A B)
    (n m : Nat) (hn : n ≤ A.size) (hnPos : 0 < n)
    (hLow : h.toCoherentTypeProfileMap.levelMap (n - 1) (by omega) < m)
    (hHigh : m ≤ h.toCoherentTypeProfileMap.levelMap n hn)
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    (hFM : F ∈ KptM family)
    (hAgree : ∀ u : TypeProfile A, u.level < n → F u.1 = h u)
    (hFront : ∀ u : TypeProfile A, u.level = n →
      (F u.1).1.1 = m ∧ F u.1 ≤ h u) :
    ∃ G : SuccessorTree.ShapeMap (admissibleKptSTree family),
      G ∈ KptM family ∧
      ∀ u : TypeProfile A, u.level ≤ n → G u.1 = h u := by
  let top := h.toCoherentTypeProfileMap.levelMap n hn
  have build : ∀ d : Nat, m + d ≤ top →
      ∃ G : SuccessorTree.ShapeMap (admissibleKptSTree family),
        G ∈ KptM family ∧
        (∀ u : TypeProfile A, u.level < n → G u.1 = h u) ∧
        (∀ u : TypeProfile A, u.level = n →
          (G u.1).1.1 = m + d ∧ G u.1 ≤ h u) := by
    intro d
    induction d with
    | zero =>
        intro _
        exact ⟨F, hFM, hAgree, by simpa only [Nat.add_zero] using hFront⟩
    | succ d ih =>
        intro hBound
        obtain ⟨G, hGM, hGa, hGf⟩ := ih (by omega)
        have hLow' : h.toCoherentTypeProfileMap.levelMap (n - 1)
            (by omega) < m + d := by omega
        have hHigh' : m + d < h.toCoherentTypeProfileMap.levelMap n hn := by
          change m + d < top
          omega
        obtain ⟨K, hKM, hKa, hKf⟩ := h.extend_front_once n (m + d)
          hn hnPos hLow' hHigh' G hGM hGa hGf
        refine ⟨K, hKM, hKa, ?_⟩
        simpa only [Nat.add_succ, Nat.add_zero] using hKf
  obtain ⟨G, hGM, hGa, hGf⟩ := build (top - m) (by omega)
  refine ⟨G, hGM, ?_⟩
  intro u hu
  by_cases huLt : u.level < n
  · exact hGa u huLt
  · have huEq : u.level = n := by omega
    obtain ⟨hGl, hGh⟩ := hGf u huEq
    have hhl : (h u).1.1 = top := by
      simpa only [huEq] using
        (h.toCoherentTypeProfileMap.levelMap_level u).symm
    apply LevelTree.same_level_of_le hGh
    change (G u.1).1.1 = (h u).1.1
    omega

/-- Every intrinsic finite type-respecting map is the literal restriction
of a member of the normalized binary monoid. No extension property is an
input hypothesis. -/
theorem «extends» (h : FiniteTypeProfileMap A B) :
    ∃ F : SuccessorTree.ShapeMap (admissibleKptSTree family),
      F ∈ KptM family ∧ ∀ u : TypeProfile A, F u.1 = h u := by
  let H := normalizedKptSMTree family
  have stages : ∀ n : Nat, n ≤ A.size →
      ∃ F : SuccessorTree.SMTree.MMap H,
        ∀ u : TypeProfile A, u.level ≤ n → F u.1 = h u := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨SuccessorTree.SMTree.MMap.id H, ?_⟩
        intro u hu
        exact (h.toCoherentTypeProfileMap.root_fixed u (by omega)).symm
    | succ n ih =>
        intro hn
        obtain ⟨F, hFa⟩ := ih (by omega)
        let G := H.closeGap F n
        obtain ⟨hGa, hGf⟩ :=
          h.toCoherentTypeProfileMap.closeGap_front_prefix n (by omega) F hFa
        let m := h.toCoherentTypeProfileMap.levelMap n (by omega) + 1
        have hLow : h.toCoherentTypeProfileMap.levelMap (n + 1 - 1)
            (by omega) < m := by simp only [Nat.add_sub_cancel]; omega
        have hHigh : m ≤ h.toCoherentTypeProfileMap.levelMap (n + 1) hn := by
          have hs := h.toCoherentTypeProfileMap.levelMap_strictMono
            (by omega : n ≤ A.size) hn (by omega : n < n + 1)
          omega
        obtain ⟨K, hKM, hKa⟩ := h.fill_front (n + 1) m hn (by omega)
          hLow hHigh G.map G.mem
          (fun u hu => hGa u (by omega)) hGf
        exact ⟨⟨K, hKM⟩, hKa⟩
  obtain ⟨F, hF⟩ := stages A.size le_rfl
  exact ⟨F.map, F.mem, fun u => hF u u.level_le_size⟩

end FiniteTypeProfileMap
end SuccessorTree.V10
