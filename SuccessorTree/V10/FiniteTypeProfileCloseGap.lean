import SuccessorTree.V10.FiniteTypeProfileRecovery
import SuccessorTree.V10.KptCompleteSMTree
import SuccessorTree.Canonical

/-!
# Starting the next finite profile front

The existing canonical gap-closing operation makes the next image level
consecutive. Agreement on the previous front and all canonical parameters
then forces its values to be the first prefixes of the prescribed next front.
-/

namespace SuccessorTree.V10

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}

namespace CoherentTypeProfileMap

variable {A B : FiniteTypeBase family}

theorem closeGap_front_prefix (h : CoherentTypeProfileMap A B)
    (n : Nat) (hn : n < A.size)
    (F : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (hAgree : ∀ u : TypeProfile A, u.level ≤ n → F u.1 = h u) :
    let G := (normalizedKptSMTree family).closeGap F n
    (∀ u : TypeProfile A, u.level ≤ n → G u.1 = h u) ∧
    (∀ u : TypeProfile A, u.level = n + 1 →
      (G u.1).1.1 = h.levelMap n (Nat.le_of_lt hn) + 1 ∧
        G u.1 ≤ h u) := by
  let H := normalizedKptSMTree family
  let G := H.closeGap F n
  have hGagree : ∀ u : TypeProfile A, u.level ≤ n → G u.1 = h u := by
    intro u hu
    exact (H.closeGap_agrees F n u.1 hu).trans (hAgree u hu)
  have hFn : H.levelMap F.map n = h.levelMap n (Nat.le_of_lt hn) := by
    let q := TypeProfile.atCut A n (Nat.le_of_lt hn)
    calc
      H.levelMap F.map n = (F q.1).1.1 := H.levelMap_eq F.map
      _ = (h q).1.1 := congrArg (fun x : AdmissibleKptNode family => x.1.1)
        (hAgree q le_rfl)
      _ = h.levelMap n (Nat.le_of_lt hn) := h.level_eq q
  have hGlevel : ∀ u : TypeProfile A, u.level = n + 1 →
      (G u.1).1.1 = h.levelMap n (Nat.le_of_lt hn) + 1 := by
    intro u hu
    calc
      (G u.1).1.1 = H.levelMap G.map u.level := (H.levelMap_eq G.map).symm
      _ = H.levelMap G.map (n + 1) := by rw [hu]
      _ = H.levelMap F.map n + 1 := H.closeGap_level_succ F n
      _ = h.levelMap n (Nat.le_of_lt hn) + 1 := by rw [hFn]
  refine ⟨hGagree, ?_⟩
  intro u hu
  refine ⟨hGlevel u hu, ?_⟩
  have hnu : n < u.level := by omega
  obtain ⟨q, c, d, hSource, hMapped, hdu⟩ := h.preserves_decomposition u n hnu
  let a := u.ancestor n (Nat.le_of_lt hnu)
  let b := u.ancestor (n + 1) (Nat.succ_le_iff.mpr hnu)
  have hb : b.1 = u.1 :=
    LevelTree.same_level_of_le (u.ancestor_le _ _) hu.symm
  have ha : G a.1 = h a := hGagree a le_rfl
  have hParams : q.map (fun p => G p.1) = q.map h := by
    apply List.map_congr_left
    intro p hp
    apply hGagree p
    have hp' : p.1 ∈ q.map Subtype.val := List.mem_map.mpr ⟨p, hp, rfl⟩
    have hlt := (admissibleKptSTree family).parameter_level_lt hSource hp'
    change p.level < n at hlt
    omega
  obtain ⟨e, hGe, heb⟩ := G.map.weak_succ' hSource
  have hGe' : (admissibleKptSTree family).succ (h a) (q.map h) c = some e := by
    simpa only [List.map_map, Function.comp_def, ha, hParams] using hGe
  have hed : e = d := Option.some.inj (hGe'.symm.trans hMapped)
  subst e
  have hdG : d ≤ G u.1 := by simpa only [hb] using heb
  have hdLevel : LevelTree.lev d = (G u.1).1.1 := by
    have hcover := (admissibleKptSTree family).covBy_of_succ_eq_some hMapped
    have hd := LevelTree.covBy_level_eq hcover
    have haLevel := h.level_eq a
    have hgu := hGlevel u hu
    change LevelTree.lev d = (h a).1.1 + 1 at hd
    change (h a).1.1 = h.levelMap n (Nat.le_of_lt hn) at haLevel
    omega
  have hdEq : d = G u.1 := LevelTree.same_level_of_le hdG hdLevel
  exact hdEq ▸ hdu

end CoherentTypeProfileMap
end SuccessorTree.V10
