import SuccessorTree.V10.ShapeMapFullRecovery
import Mathlib.Tactic

/-!
# Prescribed prefix of an actual transported canonical parameter

A canonical parameter is not merely retained at its own free cut:
all its shorter complete type prefixes occur at the same ordinary
coordinate in the upper image. The weak successor need only be below
that image node.
-/

namespace SuccessorTree.V10

/-- Restricting the type of an ordinary vertex to a smaller parameter
socle is the type over that smaller cut; all L+ atoms are kept. -/
theorem PartialTypeWithE.ordinaryType_restrict_cut {ell db du dd : Nat}
    (Q : PartialTypeWithE ell db du dd) (j : Nat) (hj : j < ell)
    (f : Nat) (hf : f ≤ ell) (n : Nat) (hn : n ≤ f) :
    (Q.ordinaryType j hj f hf).restrict hn =
      Q.ordinaryType j hj n (hn.trans hf) := by
  apply PartialTypeWithE.eq_of_atoms
  · apply RelationalPrefixType.eq_of_atoms
    · intro x y t
      cases x <;> cases y <;> rfl
    · intro x t
      cases x <;> rfl
    · intro x t
      cases x <;> rfl
  · intro x y
    cases x <;> cases y <;> rfl

/-- The entire prefix of each actual canonical source parameter is
transported as an ordinary-vertex type in the same ambient image.
This includes type vertices, negative atoms, E, and all directed bits. -/
theorem shapeMap_transports_parameter_prefix {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    (F : SuccessorTree.ShapeMap (admissibleKptSTree family))
    {a b u : AdmissibleKptNode family}
    {p : List (AdmissibleKptNode family)} {c : AdmissibleKptSigma family}
    (hSource : (admissibleKptSTree family).succ a p c = some b)
    (hBelow : b ≤ u) (v : AdmissibleKptNode family) (hv : v ∈ p)
    (n : Nat) (hn : n ≤ LevelTree.lev v) :
    ∃ (hj : LevelTree.lev (F a) < LevelTree.lev (F u))
      (hf : LevelTree.lev (F (LevelTree.ancestor v n hn)) ≤ LevelTree.lev (F u)),
      (F u).1.2.ordinaryType (LevelTree.lev (F a)) hj
         (LevelTree.lev (F (LevelTree.ancestor v n hn))) hf =
        (F (LevelTree.ancestor v n hn)).1.2 := by
  let lower := LevelTree.ancestor v n hn
  have hFPrefix : F lower ≤ F v :=
    F.map_le_of_le (LevelTree.ancestor_le v n hn)
  have hPrefixRaw : (F lower).1 ≤ (F v).1 := hFPrefix
  obtain ⟨hLe,hQ⟩ := hPrefixRaw
  obtain ⟨hj,hf,hParam⟩ :=
    shapeMap_transports_parameter_record family F hSource hBelow v hv
  have hParamRec : (F v).1.2 = (F u).1.2.ordinaryType
      (LevelTree.lev (F a)) hj (LevelTree.lev (F v)) hf :=
    eq_of_heq (Sigma.mk.inj_iff.mp hParam).2
  refine ⟨hj,le_trans hLe hf,?_⟩
  have hLower : (F lower).1.2 = (F v).1.2.restrict hLe := by
    exact hQ
  calc
    (F u).1.2.ordinaryType (LevelTree.lev (F a)) hj
        (LevelTree.lev (F lower)) (le_trans hLe hf) =
        ((F u).1.2.ordinaryType (LevelTree.lev (F a)) hj
          (LevelTree.lev (F v)) hf).restrict hLe := by
      exact (PartialTypeWithE.ordinaryType_restrict_cut
        (F u).1.2 (LevelTree.lev (F a)) hj (LevelTree.lev (F v)) hf
        (LevelTree.lev (F lower)) hLe).symm
    _ = (F v).1.2.restrict hLe := by rw [hParamRec]
    _ = (F lower).1.2 := hLower.symm

end SuccessorTree.V10
